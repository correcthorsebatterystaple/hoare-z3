import { readFileSync, writeFileSync } from 'fs';
import {
  getPostAnnotationFromNode,
  getPreAnnotiationFromNode,
  _getVerificationConditions,
} from './getVerificationConditions';
import { generateSmtText } from './smtGenerator';
import ts from 'typescript';
import { isValidParse } from './helpers/parserHelpers';
import path from 'path';
import { exec } from 'child_process';
import 'colors';

function parseArgs(_args: string[]) {
  let args = require('minimist')(_args);
  return {
    filename: args._[0],
    output: args.o || args.output || false,
    annotate: args.a || args.annotate || false,
    conditions: args.c || args.conditions || false,
    verbose: args.v || args.verbose || false,
    verify: args.verify || false,
    outputAll: args['output-all'] || false,
  };
}

function getProgramCompileErrors(filename: string): string[] {
  const program = ts.createProgram([filename], {});
  const diagnostics = ts.getPreEmitDiagnostics(program);

  // Check for compiler errors
  if (diagnostics.length > 0) {
    const messages = [];
    for (const diagnostic of diagnostics) {
      messages.push(diagnostic.messageText);
    }
    return messages;
  }
}

function getAllTopFunctionsFromSource(source: ts.SourceFile): ts.FunctionDeclaration[] {
  return source.statements.filter((x) => ts.isFunctionDeclaration(x)) as ts.FunctionDeclaration[];
}

function validateProgram(opts: { sourceFile: ts.SourceFile; filename: string;}) {
  const { sourceFile, filename } = opts;
  const compileErrors = getProgramCompileErrors(filename);
  if (compileErrors?.length > 0) {
    throw new Error(compileErrors.join('\n'));
  }

  let auxVariables = [];
  const getAuxVariables = (node: ts.Node) => {
    if (ts.isIdentifier(node) && /^_[a-zA-Z]_$/.test(node.getText())) {
      auxVariables.push(node.getText());
    }
    node.forEachChild((child) => {
      getAuxVariables(child);
    });
  };
  getAuxVariables(sourceFile);
  if (auxVariables.length > 0) {
    throw new Error(`Auxilary varibles not allowed in program: ${auxVariables.join(', ')}`);
  }

  let returnStatements = 0;
  const getReturnStatementCount = (node: ts.Node) => {
    if (ts.isReturnStatement(node)) {
      returnStatements++;
    } else {
      node.forEachChild((child) => getReturnStatementCount(child));
    }
  };
  const returnStatementsPerFunc = getAllTopFunctionsFromSource(sourceFile).map((f) => {
    returnStatements = 0;
    getReturnStatementCount(f);
    return returnStatements;
  });
  if (returnStatementsPerFunc.some(x => x > 1)) {
    throw new Error(`Max return statements exceeded`);
  }
}

function main(..._args: string[]) {
  // parse arguments
  const OPTS = parseArgs(_args);

  // validate program
  const printer = ts.createPrinter({ removeComments: false });
  const sourceText = readFileSync(OPTS.filename, 'utf-8');
  const sourceFile = ts.createSourceFile(OPTS.filename, sourceText, ts.ScriptTarget.Latest, true);

  const [mainFunc, ...otherFuncs] = getAllTopFunctionsFromSource(sourceFile);
  const mainFuncSignature = `${mainFunc.name.text}(${mainFunc.parameters.map((p) => p.name.getText()).join(', ')})`;
  const otherFuncsSignature = otherFuncs.map(
    (f) => `${f.name.text}(${f.parameters.map((p) => p.name.getText()).join(', ')})`
  );

  // validate annotations
  const precondition = getPreAnnotiationFromNode(mainFunc, sourceFile);
  if (!isValidParse(precondition)) {
    throw new Error('Invalid precondition');
  }

  const postcondition = getPostAnnotationFromNode(mainFunc, sourceFile);
  if (!isValidParse(postcondition)) {
    throw new Error('Invalid postcondition');
  }

  validateProgram({ sourceFile: sourceFile, filename: OPTS.filename });

  // get verification conditions
  const mainVerificationConditions = _getVerificationConditions(mainFunc.body, precondition, postcondition, sourceFile);
  const otherVerificationConditions = otherFuncs.map((func, i) => {
    const precondition = getPreAnnotiationFromNode(func, sourceFile);
    const postcondition = getPostAnnotationFromNode(func, sourceFile);

    return _getVerificationConditions(func.body, precondition, postcondition, sourceFile);
  });

  if (OPTS.verbose) {
    console.log('----------------CONDITIONS----------------'.blue);
    console.log(mainFuncSignature.green);
    console.log(mainVerificationConditions.join('\n'));
    otherFuncsSignature.forEach((sign, i) => {
      console.log(sign.green);
      console.log(otherVerificationConditions[i].join('\n'));
    });
  }

  // get smt text
  const mainSmtText = generateSmtText(sourceFile, precondition, mainVerificationConditions, otherFuncs);
  const otherSmtTexts = otherFuncs.map((func, i) => {
    const precondition = getPreAnnotiationFromNode(func, sourceFile);
    return generateSmtText(sourceFile, precondition, otherVerificationConditions[i], otherFuncs.slice(i + 1));
  });

  if (OPTS.verbose) {
    console.log('-----------------ANNOTATED----------------'.blue);
    console.log(printer.printFile(sourceFile));
  }

  if (OPTS.verbose) {
    console.log('------------------SMTLIB------------------'.blue);
    console.log(mainFuncSignature.green);
    console.log(mainSmtText);
    otherFuncsSignature.forEach((sign, i) => {
      console.log(sign.green);
      console.log(otherSmtTexts[i]);
    });
  }

  // annotate
  if (OPTS.annotate) {
    const { name: filename } = path.parse(OPTS.filename);
    writeFileSync(`${filename}.annotated.ts`, printer.printFile(sourceFile));
  }

  // output
  if (OPTS.output) {
    writeFileSync(OPTS.output, mainSmtText);
    if (OPTS.outputAll) {
      otherFuncs.forEach((f, i) => writeFileSync(`${f.name.text}-${OPTS.output}`, otherSmtTexts[i]));
    }
  }

  if (OPTS.verify) {
    const cmd = exec('z3 --in');

    cmd.stdout.on('data', (data) => {
      if (data.trim() === 'sat') {
        console.log('invalid');
      }

      if (data.trim() === 'unsat') {
        console.log('valid');
      }
    });
    cmd.stdin.write(mainSmtText);
    cmd.stdin.end();
  }
}

try {
  main(...process.argv.slice(2));
} catch (error) {
  console.log();
  console.error(`ERR: ${error.message}`.red);
}
