import * as ts from 'typescript';
import * as utils from 'tsutils';
import * as fs from 'fs';

const verifications = [];
const fileName = 'test.ts';
const src = ts.createSourceFile(fileName, fs.readFileSync(fileName, 'utf-8'), ts.ScriptTarget.Latest);
const main = src.statements.filter(x => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;

const [preconditionRange] = ts.getLeadingCommentRanges(src.getFullText(), main.getFullStart());
const precondition = src.getFullText().slice(preconditionRange.pos, preconditionRange.end);

const [postconditionRange] = ts.getTrailingCommentRanges(src.getFullText(), main.end);
const postcondition = src.getFullText().slice(postconditionRange.pos, postconditionRange.end);

let currentCondition = postcondition;

const reversedStatements: ts.Statement[] = [];
main.body.statements.forEach(child => reversedStatements.unshift(child));

const x1 = getVerificationCondition(reversedStatements[0], postcondition);

function getVerificationCondition(node: ts.Node, postcondition: string): string[] {
    // Assignment statement
    if (ts.isExpressionStatement(node) && ts.isBinaryExpression(node.expression) && node.expression.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(node.expression.left) && ts.isIdentifier(node.expression.right)) {
        let precondition = postcondition.replace(node.expression.left.escapedText.toString(), node.expression.right.escapedText.toString());
    }

    // If Statement
    if (ts.isIfStatement(node)) {        
        console.log(1);
    }

    return [];
}