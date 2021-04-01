//? a=_X_ AND b=_Y_ AND n>=_X_ AND n>=_Y_ AND n=_N_
function incrementDual(a: number, b: number, n: number) {
  //? a<=n AND b<=n AND n=_N_
  while (a != n) {
    a = a + 1;
  }
  a = a + 5;
  //? b<=n AND a=_N_+5 AND n=_N_
  while (b != n) {
    b = b + 1;
  }
} //? a=_N_+5 AND b=_N_
