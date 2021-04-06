import { readFileSync, writeFileSync } from 'fs';
import {
  getPostAnnotationFromNode,
  getPreAnnotiationFromNode,
  getVerificationConditions,
} from './getVerificationConditions';
import { generateSmtText } from './smtGenerator';
import ts = require('typescript');
import { prefixArrays } from './hoareTransformers';
import { Console } from 'console';

let args = require('minimist')(process.argv.slice(2));
export const OPTS = {
  filename: args._[0],
  output: args.o || args.output || false,
  annotate: args.a || args.annotate || false,
};
export const printer = ts.createPrinter({removeComments: false});

const sourceText = readFileSync(OPTS.filename, 'utf-8');

const sourceFile = ts.createSourceFile(OPTS.filename, sourceText, ts.ScriptTarget.Latest, true);

const func = sourceFile.statements.filter((x) => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;

const precondition = getPreAnnotiationFromNode(func, sourceFile);
const postcondition = getPostAnnotationFromNode(func, sourceFile);

const verificationConditions = getVerificationConditions(func.body, precondition, postcondition, sourceFile).map((v) =>
  prefixArrays(v)
);

// console.log(verificationConditions);
const smtText = generateSmtText(verificationConditions);

if (OPTS.output) {
  writeFileSync(OPTS.output, smtText);
} else {
  console.log('------------------OUTPUT------------------');
  console.log(smtText);
}

if (OPTS.annotate) {
  writeFileSync(`${OPTS.filename}.annotated.ts`, printer.printFile(sourceFile));
} else {
  console.log('-----------------ANNOTATED----------------');
  console.log(printer.printFile(sourceFile));
}
