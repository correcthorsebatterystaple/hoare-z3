import { ParserNodeType } from './enums/ParserNodeType';
import { infixToSmtPrefix } from './infixToPrefix';
import { tokenize } from './tokenizer';

/**
 * Takes an array of conditions(infix) and outputs smt source code
 * @param conditions Array of conditions that need to be asserted
 * @returns Smt source code
 */
export function generateSmtText(conditions: string[]): string {
  const checkSatStatement = '(check-sat)';
  const parts = [];

  const condition = conditions.map(x => `(${x})`).join(' AND ');
  // const condition = conditions[2];
  const prefixCondition = infixToSmtPrefix(condition);

  parts.push(generateDeclareStatements(condition));
  parts.push(generateAssertStatement(prefixCondition));
  parts.push(checkSatStatement);

  return parts.join('\n');
}

function generateDeclareStatements(str: string): string {
  const tokenizedStr = tokenize(str);
  const declareStatements = new Set<string>();

  function makeDeclareStatement(idStr: string): string {
    return `(declare-const ${idStr} Int)`;
  }

  for (const token of tokenizedStr) {
    if (token.type === ParserNodeType.Id || token.type === ParserNodeType.IdAux) {
      declareStatements.add(makeDeclareStatement(token.value));
    }
  }

  return Array.from(declareStatements).join('\n');
}

function generateAssertStatement(assertion: string): string {
  return `(assert (not ${assertion}))`;
}
