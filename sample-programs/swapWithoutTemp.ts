//? a = _X_ AND b = _Y_
function swapWithoutTemp(a: number, b: number) {
  a = a + b;
  b = a - b;
  a = a - b;
}//? a = _Y_ AND b = _X_
