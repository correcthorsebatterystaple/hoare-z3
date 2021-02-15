import * as grammar from './grammar';
import * as nearley from 'nearley';

const terminalTypes = ['id', 'integer', 'rel_op'];
const binaryOpTypes = ['bool_bin_op', 'rel_exp', 'math_op'];
const unaryOpTypes = ['bool_un_op'];

interface Node {
  type: string;
  value: string;
  child?: Node;
  left?: Node;
  right?: Node;
}

export function infixToPrefix(node: Node | string): string {
  if (!node) return;

  if (typeof node === 'string') {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(node);
    return infixToPrefix(parser.results[0]);
  }

  if (node.type === 'root') {
    return infixToPrefix(node.value);
  }

  if (terminalTypes.includes(node.type)) {
    return node.value;
  }

  // unary operator
  if (unaryOpTypes.includes(node.type)) {
    // has child of terminal type
    return `(${node.value} ${infixToPrefix(node.child)})`;
  }

  // binary operator
  if (binaryOpTypes.includes(node.type)) {
    return `(${node.value} ${infixToPrefix(node.left)} ${infixToPrefix(node.right)})`;
  }
}
