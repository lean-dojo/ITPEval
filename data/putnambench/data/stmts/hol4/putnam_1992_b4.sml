(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b4:
  the smallest possible numerator degree after differentiating the specified
  rational function 1992 times is 3984. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory polyTheory limTheory;

val putnam_1992_b4 =
  ``let valid =
      \p : real list.
        poly p <> poly [] /\
        degree p < 1992 /\
        !d : real list.
          d poly_divides p /\
          d poly_divides ([0; ~1; 0; 1] : real list)
          ==>
          degree d = 0
    in
    let pair =
      \p f : real list.
        ?g : real list.
          poly g <> poly [] /\
          !x : real.
            x <> ~1 /\ x <> 0 /\ x <> 1 /\ poly g x <> 0
            ==>
            diffn 1992
              (\y : real. poly p y / (y pow 3 - y)) x =
            poly f x / poly g x
    in
      (?p f : real list.
         valid p /\
         pair p f /\
         degree f = 3984) /\
      (!p f : real list.
         valid p /\
         pair p f
         ==>
         3984 <= degree f)``;
