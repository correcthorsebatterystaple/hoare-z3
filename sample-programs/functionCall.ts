//? a = _A_
function absolute(a: number) {
  return max(a, -a);
} //? ($ret = _A_ AND _A_>0) OR ($ret= -_A_ AND _A_<=0)

//? x = _X_ AND y = _Y_
function max(x: number, y: number) {
  let z = 0;
  if (x > y) {
    z = x;
  } else {
    z = y;
  }
  return z;
} //? $ret >= _X_ AND $ret >= _Y_ AND ($ret = _X_ OR $ret = _Y_)
