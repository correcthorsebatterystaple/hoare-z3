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

const color = require('colors/safe');

function parseArgs(_args: string[]) {
  let args = require('minimist')(_args);
  return {
    filename: args._[0],
    output: args.o || args.output || false,
    annotate: args.a || args.annotate || false,
    conditions: args.c || args.conditions || false,
    verbose: args.v || args.verbose || false,
    verify: args.verify || false,
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

function main(..._args: string[]) {
  // parse arguments
  const OPTS = parseArgs(_args);

  // validate program
  const printer = ts.createPrinter({ removeComments: false });
  const sourceText = readFileSync(OPTS.filename, 'utf-8');
  const sourceFile = ts.createSourceFile(OPTS.filename, sourceText, ts.ScriptTarget.Latest, true);

  const compileErrors = getProgramCompileErrors(OPTS.filename);
  if (compileErrors?.length > 0) {
    throw new Error(compileErrors.join('\n'));
  }

  const [firstFunc, ...otherFuncs] = getAllTopFunctionsFromSource(sourceFile);

  // validate annotations
  const precondition = getPreAnnotiationFromNode(firstFunc, sourceFile);
  if (!isValidParse(precondition)) {
    throw new Error('Invalid precondition');
  }

  const postcondition = getPostAnnotationFromNode(firstFunc, sourceFile);
  if (!isValidParse(postcondition)) {
    throw new Error('Invalid postcondition');
  }

  // get verification conditions
  const mainVerificationConditions = _getVerificationConditions(firstFunc.body, precondition, postcondition, sourceFile);
  if (OPTS.verbose) {
    console.log('----------------CONDITIONS----------------');
    console.log(mainVerificationConditions.join('\n'));
  }

  // get smt text
  const smtText = generateSmtText(sourceFile, precondition, mainVerificationConditions, otherFuncs);

  // annotate
  if (OPTS.annotate) {
    const { name: filename } = path.parse(OPTS.filename);
    writeFileSync(`${filename}.annotated.ts`, printer.printFile(sourceFile));
  }

  // output
  if (OPTS.output) {
    writeFileSync(OPTS.output, smtText);
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
    cmd.stdin.write(smtText);
    cmd.stdin.end();
  }

  if (OPTS.verbose) {
    console.log('-----------------ANNOTATED----------------');
    console.log(printer.printFile(sourceFile));
    console.log('------------------SMTLIB------------------');
    console.log(smtText);
  }
}

try {
  main(...process.argv.slice(2));
} catch (error) {
  console.log();
  console.error(color.red(`ERR: ${error.message}`));
}

