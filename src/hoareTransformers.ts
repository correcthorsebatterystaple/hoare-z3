import { LexerTokenType } from './enums/LexerTokenType';
import { ParserNodeType } from './enums/ParserNodeType';
import { tokenize } from './tokenizer';

export function assignmentTransform(postcondition: string, left: string, right: string): string {
  const replaceableTypes: string[] = [ParserNodeType.Id, ParserNodeType.ReturnId];
  const tokenizedPostcondition = tokenize(postcondition);
  return tokenizedPostcondition.reduce((acc, token) => {
    // Replace all tokens equivalent to 'left' string with 'right' string
    if (replaceableTypes.includes(token.type) && token.value === left) {
      return acc.concat('(', right, ')');
    }
    return acc.concat(token.value);
  }, '');
}

export function conditionalTransform(
  condition: string,
  thenPrecondition: string,
  elsePrecondition: string | undefined
) {
  const result = `((${thenPrecondition}) AND (${condition}))`;

  if (elsePrecondition && elsePrecondition.length) {
    return result.concat(' ', `OR ((${elsePrecondition}) AND NOT(${condition}))`);
  } else {
    return result.concat(' ', `OR NOT(${condition})`);
  }
}

export function loopTransform() {}

export function arrayStoreTransform(
  postcondition: string,
  arrayId: string,
  argId: string,
  assignment: string
): string {
  const arrayMatcher = new RegExp(
    `(${arrayId})\\s*((?:\\{\\s*\\w+\\s*<\\-\\s*\\w+\\s*\\})*)\\s*\\[\\s*(\\w+)\\s*\\]`,
    'g'
  );

  if (arrayMatcher.test(postcondition)) {
    return postcondition.replace(arrayMatcher, `$1$2{${argId}<-${assignment}}[$3]`);
  }

  return postcondition;
}

export function prefixArrays(str: string) {
  const arrayMatcher = /(?<!\!)(\w+)(?=\s*(?:\{.*?\})*\s*\[.*?\])/g;
  if (arrayMatcher.test(str)) {
    return str.replace(arrayMatcher, '!$1');
  }

  return str;
}
