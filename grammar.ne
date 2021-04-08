@{%
const moo = require('moo');
// Order is important
const lexer = moo.compile({
    implication_op: '=>',
    replace_op: '<-',
    rel_op: ['>', '>=', '<', '<=', '=', '!='],
    or_word: {match: ['or', 'OR'], value: s => 'or'},
    and_word: {match:['and', 'AND'], value: s =>'and'},
    not_word: {match:['not', 'NOT'], value: s =>'not'},
    left_para: '(',
    right_para: ')',
    plus_op: '+',
    minus_op: '-',
    mul_op: '*',
    list_sep: ',',
    div_op: '//',
    mod_op: '%',
    return_id: '$ret',
    left_array_bracket: '[',
    right_array_bracket: ']',
    left_replace_bracket: '{',
    right_replace_bracket: '}',
    array_id: /![a-zA-Z]/,
    array_id_aux: /!_[a-zA-Z]_/,
    id: /[a-zA-Z]+/,
    id_aux: {match: /_[a-zA-Z]+_/},
    integer: /\d+/,
    ws: /[ \t]/,
});
%}

@lexer lexer

b_exp
    -> _ or_exp _{% d => ({type: 'root', value: d[1]})%}
# OR expression
or_exp
    -> or_exp (__ %or_word __) and_exp {% d => ({type: 'bool_bin_op', value:d[1][1], left: d[0], right: d[2]}) %}
    |  and_exp {% id %}
# AND expression
and_exp
    -> and_exp (__ %and_word __) impl_exp {% d => ({type: 'bool_bin_op', value: d[1][1], left: d[0], right: d[2]}) %}
    |  impl_exp {% id %}
# Implication expression
impl_exp
    -> impl_exp (_ %implication_op _) not_exp {% d => ({type: 'bool_bin_op', value: d[1][1], left: d[0], right: d[2]})%}
    |  not_exp {% id %}
# NOT expression
not_exp 
    -> (%not_word _ "(" _) or_exp (_ ")") {% d => ({type: 'bool_un_op', value: d[0][0], child: d[1]})%}
    |  bool_term {% id %}
    |  "(" (_ or_exp _) ")" {% d => d[1][1] %}
# A term that returns true or false
bool_term
    -> rel_exp {% id %}
# Relational expression that compares two math expressions
rel_exp 
    -> math_exp (_ %rel_op _) math_exp {% d => ({type: 'rel_exp', value: d[1][1], left: d[0], right: d[2]})%}
    |  array_term (_ "=" _) array_term  
        {% d => ({type: 'rel_exp', value: d[1][1], left: d[0], right: d[2]})%}
    |  %id {% id %}
# Math exprssion
math_exp -> mod_term {% id %}

mod_term 
    -> mod_term (_ %mod_op _) sum_term {% d => ({type: 'math_op', value: d[1][1], left: d[0], right: d[2]})%}
    |  sum_term {% id %}
sum_term 
    -> sum_term (_ ( %plus_op | %minus_op ) _) mul_term {% d => ({type: 'math_op', value: d[1][1][0], left: d[0], right: d[2]})%}
    |  mul_term {% id %}
mul_term 
    -> mul_term (_ (%div_op | %mul_op) _) math_exp {% d => ({type: 'math_op', value: d[1][1], left: d[0], right: d[2]})%}
    |  "(" mod_term ")" {% d => d[1]%}
    |  function_call {% id %}
    |  term {% id %}
function_call
    -> %id "(" (_ arg_list _) ")" {% d => ({type: 'function_call', value: d[0], args: d[2][1]})%}
arg_list 
    -> arg_list (_ "," _) mod_term {% d => [...d[0], d[2]]%}
    |  mod_term # should return a single element array
term
    -> (%id | %integer | %id_aux | %return_id | array_selection) {% d => d[0][0] %}
array_selection
    -> array_term (_ %left_array_bracket _) mod_term (_ %right_array_bracket)
        {% d => ({type: 'array_selection', value: d[0], arg: d[2]})%}
array_term
    -> (%array_id | %array_id_aux) array_store_term:?
        {% d => ({type: 'array', value: d[0][0], store: d[1]})%}
array_store_term
    -> array_store_term (_ "{" _) mod_term (_ %replace_op _) mod_term (_ "}" _) {% d => [...d[0], [d[2],d[4]]]%}
    |  (_ "{" _) mod_term (_ %replace_op _) mod_term (_ "}" _) {% d => [[d[1],d[3]]]%}
_ -> %ws:* # optional whitespace
__ -> %ws:+ # mandatory whitespace