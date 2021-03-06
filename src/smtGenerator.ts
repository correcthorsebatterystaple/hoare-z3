import { LexerTokenType } from './enums/LexerTokenType';
import { infixToSmtPrefix } from './infixToPrefix';
import { parseAnnotation, visitParserNode } from './helpers/parserHelpers';
import { tokenize } from './tokenizer';
import { ParserNodeType } from './enums/ParserNodeType';
import { ArrayNode, FunctionNode, TerminalNode } from './interfaces/ParserNode';
import { LexerToken } from './interfaces/LexerToken';
import ts from 'typescript';
import { getPreAnnotiationFromNode, getPostAnnotationFromNode } from './getVerificationConditions';
import { BUILTIN_FUNCTIONS } from './builtin';

let assertCount = 0;

/**
 * Takes an array of conditions(infix) and outputs smt source code
 * @param verificationConditions Array of conditions that need to be asserted
 * @returns Smt source code
 */
export function generateSmtText(
  sourceFile: ts.SourceFile,
  precondition: string,
  verificationConditions: string[],
  functions: ts.FunctionDeclaration[] = []
): string {
  const smtText = [];

  const preconditionAssertStatement = generateAssertStatement(infixToSmtPrefix(precondition), { name: 'pre' }).concat(
    `; ${precondition}`
  );

  const functionDefinitions = getFunctionDefinitions(functions, sourceFile);
  const infixDefinitions = functionDefinitions.map(
    ([quantifiers, definition]) => `(forall ${quantifiers} ${infixToSmtPrefix(definition)})`
  );

  const assertDefinitions = infixDefinitions
    .map((x, idx) => generateAssertStatement(x, { name: `def!${idx}` }))
    .join('\n');
  const assertConditions = verificationConditions
    .map((x, idx) =>
      generateAssertStatement(infixToSmtPrefix(x), { negate: true, name: `veri!${idx}` }).concat(`; ${x}`)
    )
    .join('\n');

  // Add built in functions that don't exist in program
  const builtInFunctionDefinitions = Object.keys(BUILTIN_FUNCTIONS)
    .filter((name) => !functions.some((f) => f.name.text === name))
    .map((v) => BUILTIN_FUNCTIONS[v][1]);

  smtText.push(`(set-option :produce-unsat-cores true)`);
  smtText.push(generateDeclareStatements(verificationConditions, functions).join('\n'));
  smtText.push(builtInFunctionDefinitions.join('\n'));
  smtText.push('; Definitions');
  smtText.push(preconditionAssertStatement);
  smtText.push(assertDefinitions);
  smtText.push('; Verification conditions');
  smtText.push(assertConditions);
  smtText.push('(check-sat)');

  return smtText.join('\n');
}

export function generateDeclareStatements(
  conditions: string[],
  functionDeclarations: ts.FunctionDeclaration[]
): string[] {
  const intIds = new Set<string>();
  const arrayIds = new Set<string>();
  const functionIds: { [name: string]: number } = {};
  const intIdTypes: string[] = [LexerTokenType.Id, LexerTokenType.IdAux, LexerTokenType.ReturnId];

  for (const condition of conditions) {
    const parserRoot = parseAnnotation(condition);

    visitParserNode(parserRoot, (node) => {
      if (!node) return;

      if (node.type === ParserNodeType.FunctionCall) {
        const func = node as FunctionNode;
        functionIds[func.value.toString()] = func.args.length;
        return;
      }

      if (node.type === ParserNodeType.Array) {
        const array = node as ArrayNode;
        arrayIds.add(array.value.toString());
        return;
      }

      if (intIdTypes.includes(node.type)) {
        const id = node as LexerToken;
        intIds.add(id.toString());
        return;
      }
    });
  }

  const intDeclareStatements = [...intIds].map((id) => `(declare-const ${id} Int)`);
  const arrayDeclareStatements = [...arrayIds].map((id) => `(declare-const ${id} (Array Int Int))`);

  const builtInFunctions = BUILTIN_FUNCTIONS;
  // function is invalid when it is not user defined and not builtin but in the annotation
  const invalidFunctions = Object.keys(functionIds).filter(
    (name) =>
      !functionDeclarations.some((f) => f.name.text === name && f.parameters.length === functionIds[name]) &&
      !Object.keys(builtInFunctions).some(
        (builtInName) => name === builtInName && builtInFunctions[builtInName][0] === functionIds[name]
      )
  );
  if (invalidFunctions.length > 0) {
    throw new Error(
      `Undeclared functions found in annotations: ${invalidFunctions.map((name) => `${name}(${functionIds[name]})`)}`
    );
  }

  // Only declare functions that are user defined
  const functionDeclareStatements = Object.keys(functionIds)
    .filter((id) => functionDeclarations.some((f) => f.name.text === id && f.parameters.length === functionIds[id]))
    .map((key) => `(declare-fun ${key} (${Array(functionIds[key]).fill('Int').join(' ')}) Int)`);

  return intDeclareStatements.concat(arrayDeclareStatements).concat(functionDeclareStatements);
}

function getFunctionDeclareStatements(functions: [name: string, numOfArgs: number][]): string[] {
  return functions.map(([name, numOfArgs]) => `(declare-func ${name} (${Array(numOfArgs).fill('Int').join(' ')}) Int)`);
}

function getFunctionDefinitions(
  funcs: ts.FunctionDeclaration[],
  sourceFile: ts.SourceFile
): [quantifiers: string, definition: string][] {
  const toAux = (id: string) => `_${id.toUpperCase()}_`;
  const definitions: [quantifiers: string, definition: string][] = [];
  for (const func of funcs) {
    const precondition = getPreAnnotiationFromNode(func, sourceFile);
    const postcondition = getPostAnnotationFromNode(func, sourceFile);

    const parameters = func.parameters.map((param) => param.name.getText());

    const premise = `(${parameters.map((param) => `${param} = ${toAux(param)}`).join(' AND ')}) AND (${
      precondition || 'true'
    })`;
    const quantifiers = `(${parameters.map((p) => `(${p} Int) (${toAux(p)} Int)`).join(' ')})`;
    const functionSignature = `${func.name.escapedText}(${parameters.map((p) => toAux(p)).join(',')})`;
    const conclusion = postcondition.replace(/\$ret/g, functionSignature);

    definitions.push([quantifiers, `((${premise}) => (${conclusion}))`]);
  }

  return definitions;
}

function generateAssertStatement(assertion: string, opts: { negate?: boolean; name?: string } = {}): string {
  const { negate, name } = opts;
  return `(assert (! ${negate ? `(not ${assertion})` : assertion} :named ${name || `cond${assertCount++}`}))`;
}
