import * as grammar from './grammar';
import * as nearley from 'nearley';
import { ParserNodeType } from './enums/ParserNodeType';

const terminalTypes = [ParserNodeType.Id, ParserNodeType.Integer, ParserNodeType.RelOp];
const binaryOpTypes = [ParserNodeType.BoolBinaryOp, ParserNodeType.MathOp, ParserNodeType.RelExp];
const unaryOpTypes = [ParserNodeType.BoolUnaryOp];

interface ParserNode {
  type: ParserNodeType;
  value: string;
  child?: ParserNode;
  left?: ParserNode;
  right?: ParserNode;
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
  if (terminalTypes.includes(node.type)) {
    return node.value;
  }

  // unary operator
  if (unaryOpTypes.includes(node.type)) {
    return `(${node.value} ${infixToPrefix(node.child)})`;
  }

  // binary operator
  if (binaryOpTypes.includes(node.type)) {
    return `(${node.value} ${infixToPrefix(node.left)} ${infixToPrefix(node.right)})`;
  }
}
