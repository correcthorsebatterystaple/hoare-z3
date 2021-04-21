import { ParserNodeType } from "../enums/ParserNodeType";
import { LexerToken } from "./LexerToken";

export interface ParserNode {
  type: ParserNodeType;
}

export interface RootNode extends ParserNode {
  value: ParserNode;
}

export interface TerminalNode extends ParserNode {
  value: string;
}

export interface UnaryOpNode extends ParserNode {
  value: LexerToken;
  child?: ParserNode;
}

export interface BinaryOpNode extends ParserNode {
  value: LexerToken;
  left?: ParserNode;
  right?: ParserNode;
}

export interface FunctionNode extends ParserNode {
  value: LexerToken;
  args: ParserNode[];
}

export interface ArraySelectionNode extends ParserNode {
  value: ArrayNode;
  arg: ParserNode;
}

export interface ArrayNode extends ParserNode {
  value: LexerToken;
  store?: ParserNode[][];
}