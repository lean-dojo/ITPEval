(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a6:
  the value at 1 of a real polynomial satisfying the given sparse identity
  is the product of its distinct positive exponents divided by n factorial.
  This file contains no proof.
*)

let statement =
  `!n:num. !a:num->real. !b:num->num. !f:real->real.
     0 < n /\
     (!i:num. i IN (1..n) ==> 0 < b i) /\
     (!i j:num.
        i IN (1..n) /\ j IN (1..n) /\ b i = b j ==> i = j) /\
     polynomial_function f /\
     (!x:real.
        (&1 - x) pow n * f x =
        &1 + sum (1..n) (\i:num. a i * x pow (b i)))
     ==> f (&1) =
         product (1..n) (\i:num. &(b i)) / &(FACT n)`;;
