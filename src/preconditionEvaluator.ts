import ts = require('typescript');
import { assignmentTransform, conditionalTransform } from './hoareTransformers';

export function getPrecondition(
  node: ts.Node,
  postcondition: string,
  src: ts.SourceFile,
  depth: number = 0,
  debug = false
): [precondition: string, text: string] {
  if (debug) {
    console.log('--'.repeat(depth), { node: node && node.getText(src), postcondition });
  }
  if (!node) return undefined;

  // block statement
  if (ts.isBlock(node)) {
    if (node.statements.length > 0) {
      // iterate through all the statements in the block and get their precondition successively
      const precondition = node.statements.reduceRight((post, statement) => {
        const newPre = getPrecondition(statement, post, src);
        return newPre[0];
      }, postcondition);

      return [precondition, node.getText(src)];
    } else {
      return [postcondition, node.getText(src)];
    }
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
      node.expression.right.getText(src)
    );

    if (debug) {
      console.log('--'.repeat(depth), assignmentPrecondition);
    }

    return [assignmentPrecondition, node.getText(src)];
  }

  // If Statement
  if (ts.isIfStatement(node) && ts.isBinaryExpression(node.expression)) {
    let [thenPrecondition] = getPrecondition(node.thenStatement, postcondition, src, depth + 2);
    let [elsePrecondition] = getPrecondition(node.elseStatement, postcondition, src, depth + 2) || [];

    const expressionText = node.expression.getText(src);
    const conditionalPrecondition = conditionalTransform(expressionText, thenPrecondition, elsePrecondition);

    if (debug) {
      console.log('--'.repeat(depth), conditionalPrecondition);
    }

    return [conditionalPrecondition, node.getText(src)];
  }

  // While statement
  if (ts.isWhileStatement(node) && ts.isBinaryExpression(node.expression)) {
    return [getConditionFromNode(node, src), node.getText(src)];
  }

  return undefined;
}

export function getConditionFromNode(node: ts.Node, src: ts.SourceFile): string {
  const srcText = src.getFullText();
  const [firstCommentRange] = ts.getLeadingCommentRanges(srcText, node.getFullStart());
  const comment = srcText.slice(firstCommentRange.pos, firstCommentRange.end);
  if (comment.startsWith('//? ')) {
    return comment.slice(3).trim();
  }

  return undefined;
}
