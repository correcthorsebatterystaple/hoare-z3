export enum ParserNodeType {
  Id = 'id',
  Integer = 'integer',
  RelOp = 'rel_op',
  BoolBinaryOp = 'bool_bin_op',
  RelExp = 'rel_exp',
  MathOp = 'math_op',
  BoolUnaryOp = 'bool_un_op',
  Root = 'root',
  FunctionCall = 'function_call',
}
