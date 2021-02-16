import { getWeakestPreconditionFromFile } from "./preconditionEvaluator";

const args = require('minimist')(process.argv.slice(2));
const debug = args.debug || false;
const fileName = args._[0];
const toPrefix = args.prefix || false;

const result = getWeakestPreconditionFromFile(fileName, {debug: debug, toPrefix: toPrefix});

console.log(result);
