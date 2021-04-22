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

  const [mainFunc, ...otherFuncs] = getAllTopFunctionsFromSource(sourceFile);

  // validate annotations
  const precondition = getPreAnnotiationFromNode(mainFunc, sourceFile);
  if (!isValidParse(precondition)) {
    throw new Error('Invalid precondition');
  }

  const postcondition = getPostAnnotationFromNode(mainFunc, sourceFile);
  if (!isValidParse(postcondition)) {
    throw new Error('Invalid postcondition');
  }

  // get verification conditions
  const mainVerificationConditions = _getVerificationConditions(
    mainFunc.body,
    precondition,
    postcondition,
    sourceFile
  );
  const otherVerificationConditions = otherFuncs.map((func, i) => {
    const precondition = getPreAnnotiationFromNode(func, sourceFile);
    const postcondition = getPostAnnotationFromNode(func, sourceFile);

    return _getVerificationConditions(func.body, precondition, postcondition, sourceFile);
  });

  if (OPTS.verbose) {
    console.log('----------------CONDITIONS----------------'.blue);
    console.log(mainFunc.name.text.green);
    console.log(mainVerificationConditions.join('\n'));
    otherFuncs.forEach((f, i) => {
      console.log(f.name.text.green);
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
    console.log(mainFunc.name.text.green);
    console.log(mainSmtText);
    otherFuncs.forEach((f, i) => {
      console.log(f.name.text.green);
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
