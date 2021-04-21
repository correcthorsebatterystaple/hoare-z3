import ts from 'typescript'
import { getFunctionDefinitions } from './src';

const code = `
//? a = _A_ AND b=_B_
function functionCall(a:number, b:number) {
  return max(a, b);
} //? $ret = max(_A_,_B_)

//? x = _X_ AND y = _Y_
function max(x: number, y: number) {
  if (x > y) {
      return x;
  } else {
      return y;
  }
} //? $ret >= _X_ AND $ret >= _Y_ AND ($ret = _X_ OR $ret = _Y_)
`;
const s = ts.createSourceFile('testt.ts', code, ts.ScriptTarget.Latest, true);

let x = getFunctionDefinitions(s.statements.slice(1) as ts.FunctionDeclaration[], s);
