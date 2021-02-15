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

export function infixToPrefix(node: Node) {
  if (!node) return;

  if (node.type === 'root') {
    return node.value;
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
