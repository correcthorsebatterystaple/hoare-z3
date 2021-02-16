import * as ts from 'typescript';
import * as fs from 'fs';
import { assignmentTransform, conditionalTransform } from './hoareTransformers';
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

let currentCondition = rootPostcondition;
let results = [];

for (let i = main.body.statements.length - 1; i >= 0; i--) {
  const statement = main.body.statements[i];
  const annotatedStatement = getPrecondition(statement, currentCondition, src);
  results.unshift(annotatedStatement);
  currentCondition = annotatedStatement[0];
}

if (toPrefix) {
  console.log({
    precondition: infixToPrefix(rootPrecondition),
    weakestPrecondition: infixToPrefix(results[0][0]),
  });
} else {
  console.log({
    precondition: rootPrecondition,
    weakestPrecondition: results[0][0],
  });
}
