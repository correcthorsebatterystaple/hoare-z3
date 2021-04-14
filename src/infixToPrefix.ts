import * as grammar from './grammar';
import * as nearley from 'nearley';
import { ParserNodeType } from './enums/ParserNodeType';
import { LexerToken } from './interfaces/LexerToken';
import { LexerTokenType } from './enums/LexerTokenType';

const TERMINAL_TYPES = [
  LexerTokenType.Id,
  LexerTokenType.Integer,
  LexerTokenType.IdAux,
  LexerTokenType.ReturnId,
  LexerTokenType.ArrayId,
  LexerTokenType.ArrayIdAux,
];
const BINARY_OP_TYPES = [ParserNodeType.BoolBinaryOp, ParserNodeType.MathOp, ParserNodeType.RelExp];
const UNARY_OP_TYPES = [ParserNodeType.BoolUnaryOp];

interface ParserNode {
  type: ParserNodeType;
}

interface RootNode extends ParserNode {
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

interface ArraySelectionNode extends ParserNode {
  value: ArrayNode;
  arg: ParserNode;
}

interface ArrayNode extends ParserNode {
  value: LexerToken;
  store?: ParserNode[][];
}

function isNodeType<T extends ParserNode>(node: ParserNode, ...types: string[]): node is T {
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
  if (isNodeType<TerminalNode>(node, ...TERMINAL_TYPES)) {
    return node.value;
  }

  // unary operator
  if (isNodeType<UnaryOpNode>(node, ...UNARY_OP_TYPES)) {
    return `(${node.value} ${infixToSmtPrefix(node.child)})`;
  }

  // binary operator
  if (isNodeType<BinaryOpNode>(node, ...BINARY_OP_TYPES)) {
    if (node.value.value === '!=') {
      return `(not (= ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)}))`;
    }
    if (node.value.value === '//') {
      return `(div ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`;
    }
    if (node.value.value === '%') {
      return `(mod ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`;
    }
    if (['==', '==='].includes(node.value.value)) {
      return `(= ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`;
    }
    return `(${node.value} ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`;
  }

  // function call
  if (isNodeType<FunctionNode>(node, ParserNodeType.FunctionCall)) {
    return `(${node.value} ${node.args.map((arg) => infixToSmtPrefix(arg)).join(' ')})`;
  }

  // array selection
  if (isNodeType<ArraySelectionNode>(node, ParserNodeType.ArraySelection)) {
    return `(select ${infixToSmtPrefix(node.value)} ${infixToSmtPrefix(node.arg)})`;
  }

  // array
  if (isNodeType<ArrayNode>(node, ParserNodeType.Array)) {
    if (!node.store?.length) {
      return node.value.toString();
    }

    const storeArray = node.store.reduce((acc, curr) => {
      const [storeIdx, storeVal] = curr;
      return `(store ${acc} ${infixToSmtPrefix(storeIdx)} ${infixToSmtPrefix(storeVal)})`;
    }, node.value.toString());
    return storeArray;
  }

  throw new Error(`INVALID-NODE-TYPE: ${node.type}`);
}
