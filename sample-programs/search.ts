//? key=_KEY_ AND !A=!_A_ AND n=_N_
function search(key: number, A: number[], n: number) {
  let i = 0;
  let z = -1;
  //? !_A_[i]
  while(i < n && z < 0) {
    if (A[i] === key) {
      z = i;
    }
    i = i +1;
  }
  return z;
}//? !_A_[$ret]=_KEY_ OR $ret < 0