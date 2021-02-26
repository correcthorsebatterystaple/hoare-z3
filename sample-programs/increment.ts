//? b=_B_ AND a=_A_ AND _B_>=_A_
function increment(a: number, b: number) {
  //? a<=b AND b=_B_
  while (a < b) {
    a = a + 1;
  }
} //? a=_B_
