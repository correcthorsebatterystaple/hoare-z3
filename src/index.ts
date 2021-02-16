import * as ts from 'typescript';
import * as fs from 'fs';
import { infixToPrefix } from './infixToPrefix';
import { getConditionFromNode, getPrecondition } from './preconditionEvaluator';

const args = require('minimist')(process.argv.slice(2));
const debug = args.debug || false;
const fileName = args._[0];
const toPrefix = args.prefix || false;

if (debug) {
  console.log('source file : ' + fileName);
}

const src = ts.createSourceFile(fileName, fs.readFileSync(fileName, 'utf-8'), ts.ScriptTarget.Latest);
const main = src.statements.filter((x) => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;

const rootPrecondition = getConditionFromNode(main, src);

const [postconditionRange] = ts.getTrailingCommentRanges(src.getFullText(), main.end);
const rootPostcondition = src
  .getFullText()
  .slice(postconditionRange.pos + 3, postconditionRange.end)
  .trim();

const weakestPrecondition = main.body.statements.reduceRight((postcondition, curr) => {
  const [precondition] = getPrecondition(curr, postcondition, src);
  return precondition;
}, rootPostcondition)

if (toPrefix) {
  console.log({
    precondition: infixToPrefix(rootPrecondition),
    weakestPrecondition: infixToPrefix(weakestPrecondition),
  });
} else {
  console.log({
    precondition: rootPrecondition,
    weakestPrecondition: weakestPrecondition,
  });
}
