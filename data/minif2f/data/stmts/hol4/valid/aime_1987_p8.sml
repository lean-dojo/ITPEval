(*
  Statement-only formalization of miniF2F valid problem aime_1987_p8. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val aime_1987_p8 =
  ``(0 < (112 : num) /\
     (?!k : num.
        (8 : real) / 15 <
          (112 : real) / (&(112 + k) : real) /\
        (112 : real) / (&(112 + k) : real) < 7 / 13)) /\
    (!n : num.
       0 < n /\
       (?!k : num.
          (8 : real) / 15 <
            (&n : real) / (&(n + k) : real) /\
          (&n : real) / (&(n + k) : real) < 7 / 13)
       ==>
       n <= 112)``;
