(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b5:
  classification of continuously differentiable real functions that map every
  rational to a rational with the same reduced denominator. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory integerTheory realTheory real_topologyTheory limTheory;
open ratTheory real_of_ratTheory;

val putnam_2008_b5 =
  ``let continuously_differentiable =
      \f : real -> real.
        (!x : real. higher_differentiable 1 f x) /\
        (\x : real. diffn 1 f x) continuous_on UNIV
    in
    let fqsat =
      \f : real -> real.
      \q : rat.
        continuously_differentiable f /\
        ?p : rat.
          real_of_rat p = f (real_of_rat q) /\
          RATD p = RATD q
    in
    let solution =
      \f : real -> real.
        ?n : int.
          f = (\x : real. x + real_of_int n) \/
          f = (\x : real. -x + real_of_int n)
    in
      !f : real -> real.
        ((!q : rat. fqsat f q) <=> solution f)``;
