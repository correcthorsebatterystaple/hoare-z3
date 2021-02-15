import { Token } from 'nearley';
import * as grammar from './grammar';

export function tokenize(str: string): Token[] {
  if (str.length === 0) return [];

  grammar.Lexer.reset(str);
  const tokens = [];
  let token;

  while ((token = grammar.Lexer.next())) {
    if (token.type !== 'ws') {
      tokens.push(token);
    }
  }

  return tokens;
}
