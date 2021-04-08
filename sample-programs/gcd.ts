//? a=_X_ AND b=_Y_ AND a>0 AND b>0
function gcd(a: number, b: number) {
  //? gcd(a,b) = gcd(_X_,_Y_)
  while (a != b) {
    if (a > b) {
      a = a - b;
    } else {
      b = b - a;
    }
  }
  return a;
} //? $ret = gcd(_X_,_Y_)
