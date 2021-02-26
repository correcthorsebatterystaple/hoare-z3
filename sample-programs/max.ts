//? x = a AND y = b
function max(x: number, y: number) {
    if (x > y) {
        return x;
    } else {
        return y;
    }
} //? $ret >= a AND $ret >= b AND ($ret = a OR $ret = b)