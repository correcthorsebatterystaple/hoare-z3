(define-fun max ((x!1 Int) (x!2 Int)) Int (
  ite (> x!1 x!2) x!1 x!2
))
(define-fun min ((x!1 Int) (x!2 Int)) Int (
  ite (< x!1 x!2) x!1 x!2
))
(define-fun divides ((x!1 Int) (x!2 Int)) Bool (
  = (mod x!2 x!1) 0
))
(define-fun-rec gcd ((a Int) (b Int)) Int
   (if (= b 0) a (gcd b (mod a b))))
(define-fun is_sorted ((A (Array Int Int)) (n Int)) Bool (
  forall ((i Int) (j Int)) (
    => (and (>= i 0) (>= j 0) (< i n) (< j n) (<= i j)) (<= (select A i) (select A j))
  )
))
(define-fun is_perm ((A (Array Int Int)) (B (Array Int Int)) (n Int)) Bool (
  forall ((i Int)) (
    => (and (>= i 0) (< i n)) (exists ((j Int)) (= (select B j) (select A i)))
  )
))