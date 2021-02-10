// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
(function () {
function id(x) { return x[0]; }

const moo = require('moo');
const lexer = moo.compile({
    rel_op: /<|<=|>|>=|=|!=/,
    ws: /[ \t]/,
    integer: /\d+/,
    id: /[a-z]+/,
    or_word: /OR/,
    and_word: /AND/,
    not_word: /NOT/,
    left_para: /\(/,
    right_para: /\)/,
    plus_sym: /\+/,
    minus_sym: /\-/,
    mul_sym: /\*/,
    div_sym: /\//,
    list_sep: /,/
});
var grammar = {
    Lexer: lexer,
    ParserRules: [
    {"name": "b_exp", "symbols": ["_", "or_exp", "_"], "postprocess": d => ({type: 'root', value: d[1]})},
    {"name": "or_exp$subexpression$1", "symbols": ["__", (lexer.has("or_word") ? {type: "or_word"} : or_word), "__"]},
    {"name": "or_exp", "symbols": ["or_exp", "or_exp$subexpression$1", "and_exp"], "postprocess": 
        d => ({
            type: 'bool_bin_op',
            value:'or',
            left: d[0],
            right: d[2],
        }) 
            },
    {"name": "or_exp", "symbols": ["and_exp"], "postprocess": id},
    {"name": "and_exp$subexpression$1", "symbols": ["__", (lexer.has("and_word") ? {type: "and_word"} : and_word), "__"]},
    {"name": "and_exp", "symbols": ["and_exp", "and_exp$subexpression$1", "not_exp"], "postprocess": 
        d => ({
            type: 'bool_bin_op',
            value: 'and',
            left: d[0],
            right: d[2],
        }) 
            },
    {"name": "and_exp", "symbols": ["not_exp"], "postprocess": id},
    {"name": "not_exp$subexpression$1", "symbols": [(lexer.has("not_word") ? {type: "not_word"} : not_word), "_", {"literal":"("}, "_"]},
    {"name": "not_exp$subexpression$2", "symbols": ["_", {"literal":")"}]},
    {"name": "not_exp", "symbols": ["not_exp$subexpression$1", "or_exp", "not_exp$subexpression$2"], "postprocess": d => ({type: 'bool_un_op', value: 'not', child: d[1]})},
    {"name": "not_exp", "symbols": ["bool_term"], "postprocess": id},
    {"name": "not_exp$subexpression$3", "symbols": ["_", "or_exp", "_"]},
    {"name": "not_exp", "symbols": [{"literal":"("}, "not_exp$subexpression$3", {"literal":")"}], "postprocess": d => d[1][1]},
    {"name": "bool_term", "symbols": ["rel_exp"], "postprocess": id},
    {"name": "rel_exp$subexpression$1", "symbols": ["_", (lexer.has("rel_op") ? {type: "rel_op"} : rel_op), "_"]},
    {"name": "rel_exp", "symbols": ["math_exp", "rel_exp$subexpression$1", "math_exp"], "postprocess": d => ({type: 'rel_exp', value: d[1][1], left: d[0], right: d[2]})},
    {"name": "rel_exp", "symbols": [(lexer.has("id") ? {type: "id"} : id)], "postprocess": id},
    {"name": "math_exp", "symbols": ["sum_term"], "postprocess": id},
    {"name": "sum_term", "symbols": ["sum_term", /[\+\-]/, "mul_term"], "postprocess": d => ({type: 'math_op', value: d[1], left: d[0], right: d[2]})},
    {"name": "sum_term", "symbols": ["mul_term"], "postprocess": id},
    {"name": "mul_term", "symbols": ["mul_term", /[\*\/]/, "term"], "postprocess": d => ({type: 'math_op', value: d[1], left: d[0], right: d[2]})},
    {"name": "mul_term", "symbols": ["mul_term", /[\*\/]/, "function_call"]},
    {"name": "mul_term", "symbols": ["function_call"], "postprocess": id},
    {"name": "mul_term", "symbols": [{"literal":"("}, "sum_term", {"literal":")"}], "postprocess": d => d[1]},
    {"name": "mul_term", "symbols": ["term"], "postprocess": id},
    {"name": "function_call$subexpression$1", "symbols": ["_", "arg_list", "_"]},
    {"name": "function_call", "symbols": [(lexer.has("id") ? {type: "id"} : id), {"literal":"("}, "function_call$subexpression$1", {"literal":")"}], "postprocess": d => ({type: 'function_call', name: d[0], arg_list: d[2][1]})},
    {"name": "arg_list$subexpression$1", "symbols": ["_", {"literal":","}, "_"]},
    {"name": "arg_list", "symbols": ["arg_list", "arg_list$subexpression$1", "sum_term"], "postprocess": d => ({type: 'arg_list', args: [...d[0], d[2]]})},
    {"name": "arg_list", "symbols": ["sum_term"]},
    {"name": "term$subexpression$1", "symbols": [(lexer.has("id") ? {type: "id"} : id)]},
    {"name": "term$subexpression$1", "symbols": [(lexer.has("integer") ? {type: "integer"} : integer)]},
    {"name": "term", "symbols": ["term$subexpression$1"], "postprocess": d => d[0][0]},
    {"name": "_$ebnf$1", "symbols": []},
    {"name": "_$ebnf$1", "symbols": ["_$ebnf$1", (lexer.has("ws") ? {type: "ws"} : ws)], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "_", "symbols": ["_$ebnf$1"]},
    {"name": "__$ebnf$1", "symbols": [(lexer.has("ws") ? {type: "ws"} : ws)]},
    {"name": "__$ebnf$1", "symbols": ["__$ebnf$1", (lexer.has("ws") ? {type: "ws"} : ws)], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "__", "symbols": ["__$ebnf$1"]}
]
  , ParserStart: "b_exp"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();