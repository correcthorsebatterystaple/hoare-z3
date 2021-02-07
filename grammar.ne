b_exp
    -> or_exp {% d => ({type: 'root', exp: d[0]})%}
or_exp
    -> or_exp " OR " and_exp
    {%
        d => ({
            type: 'bin_op',
            op:'OR',
            left: d[0],
            right: d[2],
        }) 
    %}
    |  and_exp {% id %}
and_exp
    -> and_exp " AND " not_exp 
    {%
        d => ({
            type: 'bin_op',
            op: 'AND',
            left: d[0],
            right: d[2],
        }) 
    %}
    |  not_exp {% id %}
not_exp 
    -> "NOT(" bool_term ")" {% d => ({type: 'bool_un_op', op: 'NOT', operand: d[1]})%}
    |  bool_term {% id %}
    |  "(" or_exp ")" {% d => d[1] %}
bool_term
    -> rel_exp {% id %}
rel_exp 
    -> math_exp rel_op math_exp {% d => ({type: 'rel_op', op: d[1], left: d[0], right: d[2]})%}
    | id {% id %}
math_exp -> sum_term {% id %}
sum_term 
    -> sum_term [\+\-] mul_term {% d => ({type: 'math_op', op: d[1], left: d[0], right: d[2]})%}
    |  mul_term {% id %}
mul_term 
    -> mul_term [\*\/] term {% d => ({type: 'math_op', op: d[1], left: d[0], right: d[2]})%}
    |  mul_term [\*\/] function_call 
    | function_call {% id %}
    |  "(" sum_term ")" {% d => d[1]%}
    |  term {% id %}
function_call -> id "(" arg_list ")" {% d => ({type: 'function_call', name: d[0], arg_list: d[2]})%}
arg_list 
    -> arg_list "," sum_term {% d => ({type: 'arg_list', args: [...d[0], d[2]]})%}
    |  sum_term # should return a single element array

term -> (id | integer) {% d => d[0][0] %}
rel_op  -> (">" | ">=" | "<" | "<=" | "==" | "!=") {% d => ({type: 'terminal_rel_op', value: d[0][0]}) %}
id      -> ([a-z]:+) {% d => ({type: 'terminal_id', value: d[0][0].join('')}) %}
integer -> ([0-9]:+) {% d => ({type: 'terminal_integer', value: d[0][0].join('')}) %}