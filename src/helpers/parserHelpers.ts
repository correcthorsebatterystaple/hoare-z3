import nearley from 'nearley';
import { LexerTokenType } from '../enums/LexerTokenType';
import { ParserNodeType } from '../enums/ParserNodeType';
import grammar from '../grammar';
import { ArrayNode, ArraySelectionNode, BinaryOpNode, FunctionNode, ParserNode, RootNode, TerminalNode, UnaryOpNode } from '../interfaces/ParserNode';

export const PARSER_TERMINAL_TYPES = [
  LexerTokenType.Id,
  LexerTokenType.Integer,
  LexerTokenType.IdAux,
  LexerTokenType.ReturnId,
  LexerTokenType.ArrayId,
  LexerTokenType.ArrayIdAux,
];
export const PARSER_BINARY_OP_TYPES = [ParserNodeType.BoolBinaryOp, ParserNodeType.MathOp, ParserNodeType.RelExp];
export const PARSER_UNARY_OP_TYPES = [ParserNodeType.BoolUnaryOp];

function getParser(): nearley.Parser {
  return new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
}

export function isValidParse(str: string): boolean {
  const parser = getParser();
  try {
    parser.feed(str);
    return !!parser.results.length;
  } catch (error) {
    return false;
  }
}

export function parseAnnotation(annotation: string): RootNode {
  const parser = getParser();
  try {
    parser.feed(annotation);
    if (parser.results.length !== 1) {
      throw new Error();
    }
    return parser.results[0];
  } catch (error) {
    return undefined;
  }
}

export function visitParserNode(node: ParserNode, callback: (node: ParserNode) => void): void {
  if (!node || isParserNodeType<TerminalNode>(node, ...PARSER_TERMINAL_TYPES)) {
    callback(node);
    return;
  }
  
  if (isParserNodeType<BinaryOpNode>(node, ...PARSER_BINARY_OP_TYPES)) {
    visitParserNode(node.left, callback);
    visitParserNode(node.right, callback);
    callback(node);
    return;
  }

  if (isParserNodeType<UnaryOpNode>(node, ...PARSER_UNARY_OP_TYPES)) {
    visitParserNode(node.child, callback);
    callback(node);
    return;
  }

  if (isParserNodeType<RootNode>(node, ParserNodeType.Root)) {
    visitParserNode(node.value, callback);
    callback(node);
    return;
  }

  if (isParserNodeType<FunctionNode>(node, ParserNodeType.FunctionCall)) {
    node.args.forEach(p => visitParserNode(p, callback));
    callback(node);
    return;
  }

  if (isParserNodeType<ArrayNode>(node, ParserNodeType.Array)) {
    node.store?.forEach(pair => {
      visitParserNode(pair[0], callback);
      visitParserNode(pair[1], callback);
    });
    callback(node);
    return;
  }

  if (isParserNodeType<ArraySelectionNode>(node, ParserNodeType.ArraySelection)) {
    visitParserNode(node.value, callback);
    visitParserNode(node.arg, callback);
    callback(node);
    return;
  }
}

export function isParserNodeType<T extends ParserNode>(node: ParserNode, ...types: string[]): node is T {
  return types.length && types.includes(node.type);
}
