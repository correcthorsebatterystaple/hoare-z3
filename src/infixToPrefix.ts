import * as grammar from './grammar';
import * as nearley from 'nearley';
import { ParserNodeType } from './enums/ParserNodeType';
import { LexerToken } from './interfaces/LexerToken';

const terminalTypes = [ParserNodeType.Id, ParserNodeType.Integer, ParserNodeType.IdAux];
const binaryOpTypes = [ParserNodeType.BoolBinaryOp, ParserNodeType.MathOp, ParserNodeType.RelExp];
const unaryOpTypes = [ParserNodeType.BoolUnaryOp];

interface ParserNode {
  type: ParserNodeType;
}

interface RootNode extends ParserNode{
  value: ParserNode;
}

interface TerminalNode extends ParserNode {
  value: string;
}

interface UnaryOpNode extends ParserNode {
  value: LexerToken;
  child?: ParserNode;
}

interface BinaryOpNode extends ParserNode {
  value: LexerToken;
  left?: ParserNode;
  right?: ParserNode;
}

interface FunctionNode extends ParserNode {
  value: LexerToken;
  args: string[];
}

function isNodeType<T extends ParserNode>(node: ParserNode, ...types: ParserNodeType[]): node is T {
  return types.length && types.includes(node.type);
}

export function infixToSmtPrefix(node: ParserNode | string): string {
  if (!node) return;

  if (typeof node === 'string') {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(node);
    return infixToSmtPrefix(parser.results[0]);
  }

  // root type
  if (isNodeType<RootNode>(node, ParserNodeType.Root)) {
    return infixToSmtPrefix(node.value);
  }

  // terminal type
  if (isNodeType<TerminalNode>(node, ...terminalTypes)) {
    return node.value;
  }

  // unary operator
  if (isNodeType<UnaryOpNode>(node, ...unaryOpTypes)) {
    return `(${node.value} ${infixToSmtPrefix(node.child)})`;
  }

  // binary operator
  if (isNodeType<BinaryOpNode>(node, ...binaryOpTypes)) {
    if (node.value.value === '!=') {
      return `(not (= ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)}))`
    }
    if (node.value.value === '//') {
      return `(div ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`
    }
    if (node.value.value === '%') {
      return `(mod ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`
    }
    return `(${node.value} ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`;
  }

  // function call
  if (isNodeType<FunctionNode>(node, ParserNodeType.FunctionCall)) {
    return `(${node.value} ${node.args.join(' ')})`;
  }
}
