import * as ts from 'typescript';
import * as utils from 'tsutils';
import * as fs from 'fs';

const fileName = 'test.ts';
const src = ts.createSourceFile(fileName, fs.readFileSync(fileName, 'utf-8'), ts.ScriptTarget.Latest);
const main = src.statements.filter(x => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;

const [preconditionRange] = ts.getLeadingCommentRanges(src.getFullText(), main.getFullStart());
const rootPrecondition = src.getFullText().slice(preconditionRange.pos+2, preconditionRange.end).trim();

const [postconditionRange] = ts.getTrailingCommentRanges(src.getFullText(), main.end);
const rootPostcondition = src.getFullText().slice(postconditionRange.pos+2, postconditionRange.end).trim();

function getPrecondition(node: ts.Node, postcondition: string, depth: number = 0): [string, string] {
    console.log('--'.repeat(depth), {node: node && node.getText(src), postcondition});
    if (!node) return undefined;

    // Assignment statement
    if (ts.isExpressionStatement(node) && ts.isBinaryExpression(node.expression) && node.expression.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(node.expression.left) && ts.isIdentifier(node.expression.right)) {
        const assignmentPrecondition = postcondition.split(`${node.expression.left.escapedText}`).join(`${node.expression.right.escapedText}`);
        console.log('--'.repeat(depth), assignmentPrecondition);
        return [
            assignmentPrecondition,
            node.getText(src),
        ];
    }

    // If Statement
    if (ts.isIfStatement(node) && ts.isBinaryExpression(node.expression)) {
        let [thenPrecondition] = getPrecondition(node.thenStatement, postcondition, depth+2);
        let [elsePrecondition] = getPrecondition(node.elseStatement, postcondition, depth+2) || [];

        const thenCondition = `(${thenPrecondition}) && ${node.expression.getText(src)}`;
        console.log('--'.repeat(depth), thenCondition);

        const elseCondition = `(${elsePrecondition || 'true'}) && ~(${node.expression.getText(src)})`;
        console.log('--'.repeat(depth), elseCondition);

        const condition = `(${thenCondition}) || (${elseCondition || 'false'})`;
        console.log('--'.repeat(depth), {condition});

        return [
            condition,
            node.getText(src),
        ];
    }

    return undefined;
}

let currentCondition = rootPostcondition;
let results = [];

for (let i = main.body.statements.length-1; i >= 0; i--) {
    const statement = main.body.statements[i];
    const annotatedStatement = getPrecondition(statement, currentCondition);
    results.unshift(annotatedStatement);
}

console.log(results);
