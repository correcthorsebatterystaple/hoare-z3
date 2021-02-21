import { tokenize } from './tokenizer';

export function generateSmtFile(implication: string): string {
  const checkSatStatement = '(check-sat)';
  const parts = [];

  parts.push(generateDeclareStatements(implication));
  parts.push(generateAssertStatement(implication));
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
    if (token.type === 'id') {
      declareStatements.add(makeDeclareStatement(token.value));
    }
  }

  return Array.from(declareStatements).join('\n');
}

function generateAssertStatement(assertion: string): string {
  return `(assert (${assertion}))`;
}
