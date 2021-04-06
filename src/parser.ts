import nearley from 'nearley';
import grammar from './grammar';

export function getParser(): nearley.Parser {
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
