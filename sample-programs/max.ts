//? x = _A_ AND y = _B_
function max(x: number, y: number) {
    if (x > y) {
        return x;
    } else {
        return y;
    }
} //? $ret >= _A_ AND $ret >= _B_ AND ($ret = _A_ OR $ret = _B_)