import * as nearley from 'nearley';
import * as grammar from './grammar';

const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
const terminalTypes = ['id', 'integer', 'rel_op'];
const binaryOpTypes = ['bool_bin_op', 'rel_exp', 'math_op'];
const unaryOpTypes = ['bool_un_op'];

parser.feed(process.argv[2]);
console.log(visit(parser.results[0].value));

function visit(node) {
    if (!node) return;

    if (terminalTypes.includes(node.type)) {
        return node.value;
    }

    // unary operator
    if (unaryOpTypes.includes(node.type)) {
        // has child of terminal type
        return `(${node.value} ${visit(node.child)})`;
    }

    // binary operator with both children of terminal type
    if (binaryOpTypes.includes(node.type)) {

        return `(${node.value} ${visit(node.left)} ${visit(node.right)})`;
    }
}