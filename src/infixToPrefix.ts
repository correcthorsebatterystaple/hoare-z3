import * as grammar from './grammar';
import * as nearley from 'nearley';
import { ParserNodeType } from './enums/ParserNodeType';
import { LexerToken } from './interfaces/LexerToken';
import { LexerTokenType } from './enums/LexerTokenType';
import { ParserNode, RootNode, TerminalNode, UnaryOpNode, BinaryOpNode, FunctionNode, ArraySelectionNode, ArrayNode } from './interfaces/ParserNode';
import { isParserNodeType, PARSER_TERMINAL_TYPES, PARSER_UNARY_OP_TYPES, PARSER_BINARY_OP_TYPES } from './helpers/parserHelpers';

export function infixToSmtPrefix(node: ParserNode | string): string {
  if (!node) return;

  if (typeof node === 'string') {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(node);
    return infixToSmtPrefix(parser.results[0]);
  }

  // root type
  if (isParserNodeType<RootNode>(node, ParserNodeType.Root)) {
    return infixToSmtPrefix(node.value);
  }

  // terminal type
  if (isParserNodeType<TerminalNode>(node, ...PARSER_TERMINAL_TYPES)) {
    return node.value;
  }

  // unary operator
  if (isParserNodeType<UnaryOpNode>(node, ...PARSER_UNARY_OP_TYPES)) {
    return `(${node.value} ${infixToSmtPrefix(node.child)})`;
  }

  // binary operator
  if (isParserNodeType<BinaryOpNode>(node, ...PARSER_BINARY_OP_TYPES)) {
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
    if (node.value.value === '-' && !node.left) {
      return `(- ${infixToSmtPrefix(node.right)})`;
    } 
    return `(${node.value} ${infixToSmtPrefix(node.left)} ${infixToSmtPrefix(node.right)})`;
  }

  // function call
  if (isParserNodeType<FunctionNode>(node, ParserNodeType.FunctionCall)) {
    return `(${node.value} ${node.args.map((arg) => infixToSmtPrefix(arg)).join(' ')})`;
  }

  // array selection
  if (isParserNodeType<ArraySelectionNode>(node, ParserNodeType.ArraySelection)) {
    return `(select ${infixToSmtPrefix(node.value)} ${infixToSmtPrefix(node.arg)})`;
  }

  // array
  if (isParserNodeType<ArrayNode>(node, ParserNodeType.Array)) {
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
