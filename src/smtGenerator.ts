import { LexerTokenType } from './enums/LexerTokenType';
import { infixToSmtPrefix } from './infixToPrefix';
import { tokenize } from './tokenizer';

let assertCount = 0;

/**
 * Takes an array of conditions(infix) and outputs smt source code
 * @param conditions Array of conditions that need to be asserted
 * @returns Smt source code
 */
export function generateSmtText(conditions: string[], definitions: string[]): string {
  const checkSatStatement = '(check-sat)';
  const parts = [];
  console.log(conditions);

  const assertDefinitions = definitions.map((x, idx) => generateAssertStatement(infixToSmtPrefix(x), { name: `def!${idx}` }));
  const assertConditions = conditions.map((x, idx) => generateAssertStatement(infixToSmtPrefix(x), { negate: true, name: `veri!${idx}`}));

  const condition = conditions.map((x) => `(${x})`).join(' AND ');

  parts.push(`(set-option :produce-unsat-cores true)`);
  parts.push(generateDeclareStatements(condition));
  parts.push(...assertDefinitions);
  parts.push(...assertConditions);
  parts.push(checkSatStatement);

  return parts.join('\n');
}

function generateDeclareStatements(str: string): string {
  const tokenizedStr = tokenize(str);
  const declareStatements = new Set<string>();
  const declarableTypes: string[] = [LexerTokenType.Id, LexerTokenType.IdAux, LexerTokenType.ReturnId];

  for (const token of tokenizedStr) {
    if (declarableTypes.includes(token.type)) {
      declareStatements.add(`(declare-const ${token.value} Int)`);
    }
    if (token.type === LexerTokenType.ArrayId || token.type === LexerTokenType.ArrayIdAux) {
      declareStatements.add(`(declare-const ${token.value} (Array Int Int))`);
    }
  }

  return Array.from(declareStatements).join('\n');
}

function generateAssertStatement(assertion: string, opts: { negate?: boolean; name?: string } = {}): string {
  const { negate, name } = opts;
  return `(assert (! ${negate ? `(not ${assertion})` : assertion} :named ${name || `cond${assertCount++}`}))`;
}
