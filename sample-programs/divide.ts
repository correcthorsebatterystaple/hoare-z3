//? a = _A_ AND b = _B_ AND _A_ >= 0 AND _B_ > 0
function divide(a: number, b: number) {
  let r = a;
  let q = 0;
  //? _A_=(q*_B_)+r AND r >= 0 AND q >= 0
  while (r >= b) {
    r = r - b;
    q = q + 1;
  }
} //? _A_=(q*_B_)+r AND r >= 0 AND r < _B_
