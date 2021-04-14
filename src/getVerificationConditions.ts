import ts from 'typescript';
import { arrayStoreTransform, assignmentTransform, conditionalTransform } from './hoareTransformers';

let loopConditions: string[] = [];

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

  const conditions: string[] = [];

  const weakestPrecondition = getWeakestPrecondition(node, postcondition, source);

  // precondition implies weakest precondition
  const implication = `(${precondition}) => (${weakestPrecondition})`;
  // add loop conditions for all loops
  conditions.push(implication, ...loopConditions);

  return conditions;
}

function getWeakestPrecondition(node: ts.Node, _postcondition: string, sourceFile: ts.SourceFile, depth = 0): string {
  const postcondition = _postcondition;
  if (!node) return undefined;
  // block statement
  if (ts.isBlock(node)) {
    // iterate through all the statements  in reverse and derive the weakest precondition for the block
    return node.statements.reduceRight((acc, statement) => {
      const weakestPrecondition = getWeakestPrecondition(statement, acc, sourceFile, depth + 1);
      addLeadingAnnotation(statement, weakestPrecondition);
      return weakestPrecondition;
    }, postcondition);
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

  // Array assignment
  if (
    ts.isExpressionStatement(node) &&
    ts.isBinaryExpression(node.expression) &&
    ts.isElementAccessExpression(node.expression.left)
  ) {
    const arrayIdentifier = node.expression.left.expression.getText(sourceFile);
    const arrayArgIdentifier = node.expression.left.argumentExpression.getText(sourceFile);
    const assignedValue = node.expression.right.getText(sourceFile);

    const arrayStorePrecondition = arrayStoreTransform(
      postcondition,
      arrayIdentifier,
      arrayArgIdentifier,
      assignedValue
    );

    return arrayStorePrecondition;
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
    return invariant;
  }

  if (ts.isReturnStatement(node)) {
    const returnPrecondition = assignmentTransform(postcondition, '$ret', node.expression.getText(sourceFile));

    return returnPrecondition;
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
  const commentRanges = ts.getLeadingCommentRanges(srcText, node.getFullStart());
  if (!commentRanges?.length) {
    throwAnnotationMissingError(node, sourceFile);
  }
  const [firstCommentRange] = commentRanges;

  const comment = srcText.slice(firstCommentRange.pos, firstCommentRange.end);

  if (!comment.startsWith('//? ')) {
    throwAnnotationMissingError(node, sourceFile);
  }

  return comment.slice(3).trim();
}

/**
 * Gets the annotation what succeeds the node
 * @param node Node which preceeds the annotation
 * @param sourceFile Source code for the node
 */
export function getPostAnnotationFromNode(node: ts.Node, sourceFile: ts.SourceFile): string {
  const commentRanges = ts.getTrailingCommentRanges(sourceFile.getFullText(), node.end);
  if (!commentRanges?.length) {
    throwAnnotationMissingError(node, sourceFile);
  }
  const [firstCommentRange] = commentRanges;
  const comment = sourceFile.getFullText().slice(firstCommentRange.pos, firstCommentRange.end);

  if (!comment.startsWith('//?')) {
    throwAnnotationMissingError(node, sourceFile);
  }

  return comment.slice(3).trim();
}

function addLeadingAnnotation(node: ts.Node, annotation: string): ts.Node {
  ts.addSyntheticLeadingComment(node, ts.SyntaxKind.SingleLineCommentTrivia, `? ${annotation}`);
  return node;
}

function throwAnnotationMissingError(node: ts.Node, sourceFile: ts.SourceFile) {
  const { line, character } = sourceFile.getLineAndCharacterOfPosition(node.getFullStart());
  throw new Error(`Expected annotation at ${line + 1}:${character + 1} ${sourceFile.fileName}`);
}

export function _getVerificationConditions(
  node: ts.Block,
  precondition: string,
  postcondition: string,
  sourceFile: ts.SourceFile
): string[] {
  if (!node.statements.length) {
    return [`((${precondition}) => (${postcondition}))`];
  }

  const lastStatement = node.statements[node.statements.length - 1];
  const blockWithoutLastStatement = ts.factory.createBlock(node.statements.slice(0, -1));

  // Assignment
  if (
    ts.isExpressionStatement(lastStatement) &&
    ts.isBinaryExpression(lastStatement.expression) &&
    lastStatement.expression.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
    ts.isIdentifier(lastStatement.expression.left)
  ) {
    const newPostcondition = assignmentTransform(
      postcondition,
      lastStatement.expression.left.text,
      lastStatement.expression.right.getText(sourceFile)
    );
    return [..._getVerificationConditions(blockWithoutLastStatement, precondition, newPostcondition, sourceFile)];
  }

  // Declaration
  if (ts.isVariableStatement(lastStatement)) {
    const declaration = lastStatement.declarationList.declarations[0];

    const newPostcondition = assignmentTransform(
      postcondition,
      declaration.name.getText(sourceFile),
      declaration.initializer.getText(sourceFile)
    );

    return [..._getVerificationConditions(blockWithoutLastStatement, precondition, newPostcondition, sourceFile)];
  }

  // Conditional
  if (ts.isIfStatement(lastStatement) && ts.isBinaryExpression(lastStatement.expression)) {
    const thenBlock = stmtToBlock(lastStatement.thenStatement);
    const elseBlock = stmtToBlock(lastStatement.elseStatement);

    const expression = lastStatement.expression.getText(sourceFile);

    const thenPre = `((${precondition}) AND (${expression}))`;
    const thenVC = _getVerificationConditions(thenBlock, thenPre, postcondition, sourceFile);

    const weakestPrecondition = getWeakestPrecondition(lastStatement, postcondition, sourceFile);
    const blockWithoutLastStatementVC = _getVerificationConditions(
      blockWithoutLastStatement,
      precondition,
      weakestPrecondition,
      sourceFile
    );
    
    const VC = [...blockWithoutLastStatementVC, ...thenVC];

    if (elseBlock) {
      const elsePre = `((${precondition}) AND NOT (${expression}))`;
      const elseVC = _getVerificationConditions(elseBlock, elsePre, postcondition, sourceFile);

      return VC.concat(elseVC);
    }

    return VC;
  }

  // While
  if (ts.isWhileStatement(lastStatement) && ts.isBinaryExpression(lastStatement.expression)) {
    const invariant = getPreAnnotiationFromNode(lastStatement, sourceFile);
    const condition = lastStatement.expression.getFullText(sourceFile);

    const whileBlock = stmtToBlock(lastStatement.statement);

    return [
      // Conditions for preceeding statements
      ..._getVerificationConditions(blockWithoutLastStatement, precondition, invariant, sourceFile),
      // Conditions for invariant validity
      ..._getVerificationConditions(whileBlock, `((${invariant}) AND (${condition}))`, invariant, sourceFile),
      // Conditions for postcondition strengthening
      `(((${invariant}) AND NOT (${condition})) => (${postcondition}))`,
    ];
  }

  // Return
  if (ts.isReturnStatement(lastStatement)) {
    const newPostcondition = assignmentTransform(postcondition, '$ret', lastStatement.expression.getText(sourceFile));
    return [..._getVerificationConditions(blockWithoutLastStatement, precondition, newPostcondition, sourceFile)];
  }

  throw new Error(`Cannot recognise node: ${lastStatement.getText(sourceFile)}`);
}

function stmtToBlock(stmt: ts.Statement | ts.Block): ts.Block {
  if (!stmt) return undefined;
  if (ts.isBlock(stmt)) {
    return stmt;
  }

  return ts.factory.createBlock([stmt]);
}
