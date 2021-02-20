//? a = x AND b = y
function swapWithoutTemp(a: number, b: number) {
  a = a + b;
  b = a - b;
  a = a - b;
}//? a = y AND b = x
