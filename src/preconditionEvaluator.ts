import { readFileSync } from 'fs';
import ts = require('typescript');
import { assignmentTransform, conditionalTransform } from './hoareTransformers';
import { infixToPrefix } from './infixToPrefix';

export class SourceInformation {
  private sourceFile: ts.SourceFile;
  private main: ts.FunctionDeclaration;
  public mainPrecondition: string;
  public mainPostcondition: string;

  constructor(private fileName: string, private sourceText: string) {
    this.sourceFile = ts.createSourceFile(this.fileName, this.sourceText, ts.ScriptTarget.Latest);
    this.main = this.sourceFile.statements.filter((x) => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;

    this.mainPrecondition = this.getPreconditionFromNode(this.main);

    const [postconditionRange] = ts.getTrailingCommentRanges(this.sourceFile.getFullText(), this.main.end);
    this.mainPostcondition = this.sourceFile
      .getFullText()
      .slice(postconditionRange.pos + 3, postconditionRange.end)
      .trim();
  }

  getMainWeakestPrecondition(
    node: ts.Node = this.main.body,
    postcondition: string = this.mainPostcondition,
    opt?: { depth?: number; debug?: boolean }
  ): string {
    const depth = opt?.depth || 0;
    const debug = opt?.debug || false;

    if (debug) {
      console.log('--'.repeat(depth), { node: node?.getText(this.sourceFile), postcondition });
    }

    if (!node) return undefined;

    // block statement
    if (ts.isBlock(node)) {
      // iterate through all the statements  in reverse and derive the weakest precondition for the block
      return node.statements.reduceRight(
        (acc, statement) => this.getMainWeakestPrecondition(statement, acc, { depth: depth + 2 }),
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
        node.expression.right.getText(this.sourceFile)
      );

      if (debug) {
        console.log('--'.repeat(depth), assignmentPrecondition);
      }

      return assignmentPrecondition;
    }

    // If Statement
    if (ts.isIfStatement(node) && ts.isBinaryExpression(node.expression)) {
      let thenPrecondition = this.getMainWeakestPrecondition(node.thenStatement, postcondition, { depth: depth + 2 });
      let elsePrecondition = this.getMainWeakestPrecondition(node.elseStatement, postcondition, { depth: depth + 2 });

      const expressionText = node.expression.getText(this.sourceFile);
      const conditionalPrecondition = conditionalTransform(expressionText, thenPrecondition, elsePrecondition);

      if (debug) {
        console.log('--'.repeat(depth), conditionalPrecondition);
      }

      return conditionalPrecondition;
    }

    // While statement
    if (ts.isWhileStatement(node) && ts.isBinaryExpression(node.expression)) {
      return this.getPreconditionFromNode(node);
    }

    throw new Error(`Node of type "${ts.SyntaxKind[node.kind]}" not implemented`);
  }

  private getPreconditionFromNode(node: ts.Node): string {
    const srcText = this.sourceFile.getFullText();
    const [firstCommentRange] = ts.getLeadingCommentRanges(srcText, node.getFullStart());

    const comment = srcText.slice(firstCommentRange.pos, firstCommentRange.end);

    if (comment.startsWith('//? ')) {
      return comment.slice(3).trim();
    }

    throw new Error(`"${comment.slice(0, 10)}${comment.length > 10 ? '...' : ''}" does not begin with "//? "`);
  }
}
