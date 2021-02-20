import { readFileSync } from 'fs';
import { getWeakestPrecondition, SourceInformation } from './preconditionEvaluator';

const args = require('minimist')(process.argv.slice(2));
const debug = args.debug || false;
const fileName = args._[0];
const toPrefix = args.prefix || false;

const sourceText = readFileSync(fileName, 'utf-8');
const sourceInfo = new SourceInformation(fileName, sourceText);

const weakestPrecondition = sourceInfo.getMainWeakestPrecondition();

console.log(weakestPrecondition);
