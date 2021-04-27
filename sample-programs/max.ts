//? x = _A_ AND y = _B_
function max(x: number, y: number) {
  let z = 0;
  if (x > y) {
    z = x;
  } else {
    z = y;
  }
  return z;
} //? $ret >= _A_ AND $ret >= _B_ AND ($ret = _A_ OR $ret = _B_)
