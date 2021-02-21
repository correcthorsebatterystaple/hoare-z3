//? b=x AND a=y AND x>=y
function increment(a: number, b: number) {
  //? a<=b
  while (a < b) {
    a = a + 1;
  }
} //? a=x
