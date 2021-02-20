@{%
const moo = require('moo');
const lexer = moo.compile({
    rel_op: ['>', '>=', '<', '<=', '=', '!='],
    ws: /[ \t]/,
    integer: /\d+/,
    or_word: ['or', 'OR'],
    and_word: ['and', 'AND'],
    not_word: ['not', 'NOT'],
    id: /[a-zA-Z]+/,
    left_para: /\(/,
    right_para: /\)/,
    plus_sym: /\+/,
    minus_sym: /\-/,
    mul_sym: /\*/,
    div_sym: /\//,
    list_sep: /,/
});
%}

@lexer lexer

b_exp
    -> _ or_exp _{% d => ({type: 'root', value: d[1]})%}
# OR expression
or_exp
    -> or_exp (__ %or_word __) and_exp
    {%
        d => ({
            type: 'bool_bin_op',
            value:'or',
            left: d[0],
            right: d[2],
        }) 
    %}
    |  and_exp {% id %}
# AND expression
and_exp
    -> and_exp (__ %and_word __) not_exp 
    {%
        d => ({
            type: 'bool_bin_op',
            value: 'and',
            left: d[0],
            right: d[2],
        }) 
    %}
    |  not_exp {% id %}
# NOT expression
not_exp 
    -> (%not_word _ "(" _) or_exp (_ ")") {% d => ({type: 'bool_un_op', value: 'not', child: d[1]})%}
    |  bool_term {% id %}
    |  "(" (_ or_exp _) ")" {% d => d[1][1] %}
# A term that returns true or false
bool_term
    -> rel_exp {% id %}
# Relational expression that compares two math expressions
rel_exp 
    -> math_exp (_ %rel_op _) math_exp {% d => ({type: 'rel_exp', value: d[1][1], left: d[0], right: d[2]})%}
    | %id {% id %}
# Math exprssion
math_exp -> sum_term {% id %}
sum_term 
    -> sum_term (_ [\+\-] _) mul_term {% d => ({type: 'math_op', value: d[1][1], left: d[0], right: d[2]})%}
    |  mul_term {% id %}
mul_term 
    -> mul_term (_ [\*\/] _) term {% d => ({type: 'math_op', value: d[1][1], left: d[0], right: d[2]})%}
    |  mul_term (_ [\*\/] _) function_call 
    | function_call {% id %}
    |  "(" sum_term ")" {% d => d[1]%}
    |  term {% id %}
function_call -> %id "(" (_ arg_list _) ")" {% d => ({type: 'function_call', name: d[0], arg_list: d[2][1]})%}
arg_list 
    -> arg_list (_ "," _) sum_term {% d => ({type: 'arg_list', args: [...d[0], d[2]]})%}
    |  sum_term # should return a single element array
term -> (%id | %integer) {% d => d[0][0] %}

_ -> %ws:* # optional whitespace
__ -> %ws:+ # mandatory whitespace