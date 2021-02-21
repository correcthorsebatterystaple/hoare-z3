import { fstat, readFileSync, writeFileSync } from 'fs';
import { infixToPrefix } from './infixToPrefix';
import { SourceInformation } from './SourceInformation';
import { generateSmtFile } from './smtGenerator';

const args = require('minimist')(process.argv.slice(2));
const debug = args.debug || false;
const fileName = args._[0];
const output = args.o || args.output || false;

const sourceText = readFileSync(fileName, 'utf-8');
const sourceInfo = new SourceInformation(fileName, sourceText);

const prefixWeakestPrecondition = sourceInfo.getMainWeakestPrecondition({prefix: true, debug});
const prefixMainPrecondition = sourceInfo.prefixMainPrecondition;
const smtSourceText = generateSmtFile(`not (=> ${prefixMainPrecondition} ${prefixWeakestPrecondition})`);

if (output) {
  writeFileSync(output, smtSourceText);
} else {
  console.log(smtSourceText);
}
