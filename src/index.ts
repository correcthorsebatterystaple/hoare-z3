import { readFileSync, writeFileSync } from 'fs';
import {
  getPostAnnotationFromNode,
  getPreAnnotiationFromNode,
  getVerificationConditions,
  _getVerificationConditions,
} from './getVerificationConditions';
import { generateSmtText } from './smtGenerator';
import ts from 'typescript';
import { isValidParse } from './parser';
import path from 'path';

let args = require('minimist')(process.argv.slice(2));
export const OPTS = {
  filename: args._[0],
  output: args.o || args.output || false,
  annotate: args.a || args.annotate || false,
};

const printer = ts.createPrinter({ removeComments: false });

const sourceText = readFileSync(OPTS.filename, 'utf-8');

const sourceFile = ts.createSourceFile(OPTS.filename, sourceText, ts.ScriptTarget.Latest, true);

const func = sourceFile.statements.filter((x) => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;

const precondition = getPreAnnotiationFromNode(func, sourceFile);
if (!isValidParse(precondition)) {
  throw new Error('Invalid precondition');
}

const postcondition = getPostAnnotationFromNode(func, sourceFile);
if (!isValidParse(postcondition)) {
  throw new Error('Invalid postcondition');
}

// _getVerificationConditions(func.body, precondition, postcondition, sourceFile).forEach(x => console.log(x));
// process.exit();
// const verificationConditions = getVerificationConditions(func.body, precondition, postcondition, sourceFile);
const verificationConditions = _getVerificationConditions(func.body, precondition, postcondition, sourceFile);

const smtText = generateSmtText(verificationConditions, [precondition]);

if (OPTS.output) {
  writeFileSync(OPTS.output, smtText);
} else {
  console.log('------------------OUTPUT------------------');
  console.log(smtText);
}

if (OPTS.annotate) {
  const {name: filename} = path.parse(OPTS.filename);
  writeFileSync(`${filename}.annotated.ts`, printer.printFile(sourceFile));
  console.log('-----------------ANNOTATED----------------');
  console.log(printer.printFile(sourceFile));
}

function hasAuxVariables(node: ts.Node, sourceFile: ts.SourceFile): boolean {
  return false;
}

function hasLoops(block: ts.Block) {
  block
}

