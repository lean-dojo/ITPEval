(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b3:
  finite iteration of the same-color distance recoloring of the positive
  reals eventually makes every positive real red. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val putnam_2022_b3 =
  ``let recolor =
      \isred : real -> bool.
        \d : real.
          ?p q : real.
            0 < p /\ 0 < q /\ p < q /\
            isred p = isred q /\ q - p = d
    in
    let putnam_2022_b3_solution = T
    in
      ((!isred : real -> bool.
          ?k : num.
            !p : real.
              0 < p ==> FUNPOW recolor k isred p)
       <=>
       putnam_2022_b3_solution)``;
