(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a1:
  a free-throw success rate that moves from below 80 percent to above
  80 percent must equal 80 percent at an intermediate prefix. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2004_a1 =
  ``!S : (num -> bool) -> num -> real.
      (!attempts : num -> bool. !N : num.
         1 <= N
         ==>
         S attempts N =
           SIGMA
             (\i : num. if attempts i then 1 else 0)
             (count N) /
           &N)
      ==>
      !attempts : num -> bool. !a b : num.
        1 <= a /\
        a < b /\
        S attempts a < 4 / 5 /\
        4 / 5 < S attempts b
        ==>
        ?c : num.
          a < c /\
          c < b /\
          S attempts c = 4 / 5``;
