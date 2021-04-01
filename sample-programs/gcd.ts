//? a=x AND b=y AND a>0 AND b>0
function gcd(a: number, b: number) {
  //? 
  while (a!=b) {
    if (a>b) {
      a = a-b;
    } else {
      b=b-a;
    }
  }
}