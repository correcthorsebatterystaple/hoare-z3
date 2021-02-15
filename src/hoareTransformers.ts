import { IfStatement } from 'typescript';
import { LexerToken } from './interfaces/LexerToken';
import { mergeTokens, tokenize } from './tokenizer';

export function assignmentTransform(postcondition: string, left: string, right: string): string {
  const tokenizedPostcondition = tokenize(postcondition);
  return tokenizedPostcondition.map((token) => {
    if (token.type === 'id' && token.value === left) {
      token.text = right;
      token.value = right;
    }
    return token;
  }).join('');
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
