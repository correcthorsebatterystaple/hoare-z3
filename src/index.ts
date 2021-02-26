import { readFileSync, writeFileSync } from 'fs';
import {
  getPostAnnotationFromNode,
  getPreAnnotiationFromNode,
  getVerificationConditions,
} from './getVerificationConditions';
import { generateSmtText } from './smtGenerator';
import ts = require('typescript');
import { infixToSmtPrefix } from './infixToPrefix';

let args = require('minimist')(process.argv.slice(2));
const fileName = args._[0];
const output = args.o || args.output || false;

const sourceText = readFileSync(fileName, 'utf-8');

const sourceFile = ts.createSourceFile(fileName, sourceText, ts.ScriptTarget.Latest);

const func = sourceFile.statements.filter((x) => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;
const precondition = getPreAnnotiationFromNode(func, sourceFile);
const postcondition = getPostAnnotationFromNode(func, sourceFile);

const verificationConditions = getVerificationConditions(func.body, precondition, postcondition, sourceFile);
console.log(verificationConditions);
const smtText = generateSmtText(verificationConditions);

if (output) {
  writeFileSync(output, smtText);
} else {
  console.log(smtText);
}
