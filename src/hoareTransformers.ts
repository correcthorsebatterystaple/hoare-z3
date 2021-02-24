import { tokenize } from './tokenizer';

export function assignmentTransform(postcondition: string, left: string, right: string): string {
  const tokenizedPostcondition = tokenize(postcondition);
  return tokenizedPostcondition.reduce((acc, token) => {
    // Replace all tokens equivalent to 'left' string with 'right' string
    if (token.type === 'id' && token.value === left) {
      return acc.concat('(', right, ')');
    }
    return acc.concat(token.text);
  }, "");
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
