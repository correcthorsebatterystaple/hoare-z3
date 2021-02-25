import ts = require('typescript');
import { assignmentTransform, conditionalTransform } from './hoareTransformers';


let loopConditions: string[] = [];
let globalPrecondition = "";

/**
 * Given the node it returns a set of verification conditions that confirm the correctness of the code
 * @param node TS Node for which the verification conditions are generated
 * @param precondition Boolean statement true before node
 * @param postcondition Boolean statement true after node
 * @param source Source text of the code
 */
export function getVerificationConditions(
  node: ts.Node,
  precondition: string,
  postcondition: string,
  source: ts.SourceFile
): string[] {
  loopConditions = [];
  globalPrecondition = precondition;

  const conditions: string[] = [];

  // precondition implies weakest precondition
  const c1 = `(${precondition}) => (${getWeakestPrecondition(node, postcondition, source)})`;
  // add loop conditions for all loops
  conditions.push(c1, ...loopConditions);

  return conditions;
}

function getWeakestPrecondition(node: ts.Node, postcondition: string, sourceFile: ts.SourceFile, depth = 0): string {
  if (!node) return undefined;
  // block statement
  if (ts.isBlock(node)) {
    // iterate through all the statements  in reverse and derive the weakest precondition for the block
    return node.statements.reduceRight(
      (acc, statement) => getWeakestPrecondition(statement, acc, sourceFile, depth + 1),
      postcondition
    );
  }

  // Assignment statement
  if (
    ts.isExpressionStatement(node) &&
    ts.isBinaryExpression(node.expression) &&
    node.expression.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
    ts.isIdentifier(node.expression.left)
  ) {
    // replaces all occurences of left side of assignment with right side of assignment in postcondition
    const assignmentPrecondition = assignmentTransform(
      postcondition,
      node.expression.left.text,
      node.expression.right.getText(sourceFile)
    );

    return assignmentPrecondition;
  }

  // variable statement
  if (ts.isVariableStatement(node)) {
    const declaration = node.declarationList.declarations[0];

    if (!declaration || !declaration.initializer) {
      return postcondition;
    }

    const assignmentPrecondition = assignmentTransform(
      postcondition,
      declaration.name.getText(sourceFile),
      declaration.initializer.getText(sourceFile)
    );

    return assignmentPrecondition;
  }

  // If Statement
  if (ts.isIfStatement(node) && ts.isBinaryExpression(node.expression)) {
    let thenPrecondition = getWeakestPrecondition(node.thenStatement, postcondition, sourceFile, depth + 1);
    let elsePrecondition = getWeakestPrecondition(node.elseStatement, postcondition, sourceFile, depth + 1);

    const expressionText = node.expression.getText(sourceFile);
    const conditionalPrecondition = conditionalTransform(expressionText, thenPrecondition, elsePrecondition);

    return conditionalPrecondition;
  }

  // While statement
  if (ts.isWhileStatement(node) && ts.isBinaryExpression(node.expression)) {
    const invariant = getPreAnnotiationFromNode(node, sourceFile);
    const condition = node.expression.getFullText(sourceFile);
    const invariantWeakestPrecondition = getWeakestPrecondition(node.statement, invariant, sourceFile, depth + 1);
    loopConditions.push(
      // invariant and condition => invariant
      `((${invariant}) AND (${condition})) => (${invariantWeakestPrecondition})`,
      // invariant and not(condition) => postcondition
      `((${invariant}) AND NOT(${condition})) => (${postcondition})`
    );
    return invariant;
  }

  throw new Error(`Node of type "${ts.SyntaxKind[node.kind]}" not implemented`);
}

/**
 * Gets the annotation that is preceeds the node
 * @param node Node which succeeds the annotation
 * @param sourceFile Source code for the node
 */
export function getPreAnnotiationFromNode(node: ts.Node, sourceFile: ts.SourceFile): string {
  const srcText = sourceFile.getFullText();
  const [firstCommentRange] = ts.getLeadingCommentRanges(srcText, node.getFullStart());

  const comment = srcText.slice(firstCommentRange.pos, firstCommentRange.end);

  if (comment.startsWith('//? ')) {
    return comment.slice(3).trim();
  }

  throw new Error(`"${comment.slice(0, 10)}${comment.length > 10 ? '...' : ''}" does not begin with "//? "`);
}

/**
 * Gets the annotation what succeeds the node
 * @param node Node which preceeds the annotation
 * @param sourceFile Source code for the node
 */
export function getPostAnnotationFromNode(node: ts.Node, sourceFile: ts.SourceFile): string {
  const [firstCommentRange] = ts.getTrailingCommentRanges(sourceFile.getFullText(), node.end);
  const comment = sourceFile.getFullText().slice(firstCommentRange.pos, firstCommentRange.end);

  if (comment.startsWith('//?')) {
    return comment.slice(3).trim();
  }

  throw new Error(`"${comment.slice(0, 10)}${comment.length > 10 ? '...' : ''}" does not begin with "//? "`);
}
