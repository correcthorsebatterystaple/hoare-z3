import * as ts from 'typescript';
import * as utils from 'tsutils';
import * as fs from 'fs';

const verifications = [];

const fileName = process.argv[2];
console.log('source file : '+ fileName)
const src = ts.createSourceFile(fileName, fs.readFileSync(fileName, 'utf-8'), ts.ScriptTarget.Latest);
const main = src.statements.filter(x => ts.isFunctionDeclaration(x))[0] as ts.FunctionDeclaration;

const rootPrecondition = getConditionFromNode(main);

const [postconditionRange] = ts.getTrailingCommentRanges(src.getFullText(), main.end);
const rootPostcondition = src.getFullText().slice(postconditionRange.pos+3, postconditionRange.end).trim();

function getPrecondition(node: ts.Node, postcondition: string, depth: number = 0): [precondition: string, text: string] {
    console.log('--'.repeat(depth), {node: node && node.getText(src), postcondition});
    if (!node) return undefined;

    // block statement
    if (ts.isBlock(node)) {
        if (node.statements.length > 0) {
            // iterate through all the statements in the block and get their precondition successively
            const precondition = node.statements.reduceRight((post, statement) => {
                const newPre = getPrecondition(statement, post);
                return newPre[0];
            }, postcondition);

            return [
                precondition,
                node.getText(src),
            ]

        } else {
            return [
                postcondition,
                node.getText(src),
            ]
        }
        
    }

    // Assignment statement
    if (ts.isExpressionStatement(node) && ts.isBinaryExpression(node.expression) && node.expression.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(node.expression.left) && ts.isIdentifier(node.expression.right)) {
        // replaces all occurences of left side of assignment with right side of assignment in postcondition
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

    // While statement
    if (ts.isWhileStatement(node) && ts.isBinaryExpression(node.expression)) {
        return [
            getConditionFromNode(node),
            node.getText(src)
        ];
    }

    return undefined;
}

function getConditionFromNode(node: ts.Node): string {
    const srcText = src.getFullText();
    const [firstCommentRange] = ts.getLeadingCommentRanges(srcText, node.getFullStart());
    const comment = srcText.slice(firstCommentRange.pos, firstCommentRange.end);
    if (comment.startsWith('//? ')) {
        return comment.slice(3).trim();
    }

    return undefined;
}

let currentCondition = rootPostcondition;
let results = [];

for (let i = main.body.statements.length-1; i >= 0; i--) {
    const statement = main.body.statements[i];
    const annotatedStatement = getPrecondition(statement, currentCondition);
    results.unshift(annotatedStatement);
    currentCondition = annotatedStatement[0];
}



console.log(results);
