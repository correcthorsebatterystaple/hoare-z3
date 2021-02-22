import * as grammar from './grammar';
import * as nearley from 'nearley';
import { ParserNodeType } from './enums/ParserNodeType';

const terminalTypes = [ParserNodeType.Id, ParserNodeType.Integer, ParserNodeType.RelOp];
const binaryOpTypes = [ParserNodeType.BoolBinaryOp, ParserNodeType.MathOp, ParserNodeType.RelExp];
const unaryOpTypes = [ParserNodeType.BoolUnaryOp];

interface ParserNode {
  type: ParserNodeType;
  value: string;
}

interface TerminalNode extends ParserNode {
  text: string;
}

interface UnaryOpNode extends ParserNode {
  child?: ParserNode;
}

interface BinaryOpNode extends ParserNode {
  left?: ParserNode;
  right?: ParserNode;
}

interface FunctionNode extends ParserNode {
  args: string[];
}

function isNodeType<T extends ParserNode>(node: ParserNode, ...types: ParserNodeType[]): node is T {
  return types.length && types.includes(node.type);
}

export function infixToPrefix(node: ParserNode | string): string {
  if (!node) return;

  if (typeof node === 'string') {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(node);
    return infixToPrefix(parser.results[0]);
  }

  // root type
  if (node.type === ParserNodeType.Root) {
    return infixToPrefix(node.value);
  }

  // terminal type
  if (isNodeType<TerminalNode>(node, ...terminalTypes)) {
    return node.value;
  }

  // unary operator
  if (isNodeType<UnaryOpNode>(node, ...unaryOpTypes)) {
    return `(${node.value} ${infixToPrefix(node.child)})`;
  }

  // binary operator
  if (isNodeType<BinaryOpNode>(node, ...binaryOpTypes)) {
    return `(${node.value} ${infixToPrefix(node.left)} ${infixToPrefix(node.right)})`;
  }

  // function call
  if (isNodeType<FunctionNode>(node, ParserNodeType.FunctionCall)) {
    return `(${node.value} ${node.args.join(' ')})`;
  }
}
