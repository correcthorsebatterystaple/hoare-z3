import * as grammar from './grammar';
import { LexerToken } from './interfaces/LexerToken';

export function tokenize(str: string): LexerToken[] {
  if (str.length === 0) return [];

  grammar.Lexer.reset(str);
  const tokens = [];
  let token: LexerToken;

  while ((token = grammar.Lexer.next() as LexerToken)) {
    tokens.push(token);
  }

  return tokens;
}

export function mergeTokens(tokens: LexerToken[]): string {
  return tokens.join('');
}
