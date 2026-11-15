(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b4:
  cyclic sequences of distinct real numbers whose consecutive triples form
  three-term arithmetic progressions exist exactly for multiples of three at
  least nine. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory realTheory;

val putnam_2022_b4 =
  ``!n : num.
      4 <= n
      ==>
      let ap3 =
        \x0 x1 x2 : real.
          !o0 o1 o2 : real.
            o0 < o1 /\
            o1 < o2 /\
            {o0; o1; o2} = {x0; x1; x2}
            ==>
            o1 - o0 = o2 - o1
      in
      let xprog =
        \x : num -> real.
          (!i j : num.
             i < n /\ j < n /\ i <> j
             ==>
             x i <> x j) /\
          (!i : num.
             i < n
             ==>
             ap3 (x i) (x ((i + 1) MOD n)) (x ((i + 2) MOD n)))
      in
        ((?x : num -> real. xprog x) <=>
         9 <= n /\ divides 3 n)``;
