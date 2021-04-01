//? n>=0 AND m>=0 AND n<len AND m<len AND n=_N_ AND m=_M_ AND A[_M_]=_AM_ AND A[_N_]=_AN_
function arraySwap(n: number, m: number, A: number[]) {
  let temp = A[n];
  A[n] = A[m];
  A[m] = temp;
} //? A[_N_] = _AM_ AND A[_M_] = _AN_
