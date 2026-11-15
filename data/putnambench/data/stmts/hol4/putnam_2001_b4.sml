(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b4:
  emptiness of the intersection of all positive iterate images of the
  nonexceptional rationals under x maps to x - 1/x. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory ratTheory;

val putnam_2001_b4 =
  ``let S =
      \x : rat.
        x <> rat_ainv 1q /\ x <> 0q /\ x <> 1q
    in
    let f =
      \x : rat. x - 1q / x
    in
    let putnam_2001_b4_solution = T
    in
      (~(?y : rat.
           !n : num.
             1 <= n
             ==>
             ?x : rat.
               S x /\ FUNPOW f n x = y)
       <=>
       putnam_2001_b4_solution)``;
