(*
  Statement-only formalization of miniF2F artifact imo_1992_p1: classification of strictly
  increasing integer triples satisfying a divisibility condition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val imo_1992_p1 =
  ``!p q r : int.
      1 < p /\ p < q /\ q < r /\
      ((p - 1) * (q - 1) * (r - 1)) int_divides
        (p * q * r - 1)
      ==>
      (p, q, r) = (2, 4, 8) \/
      (p, q, r) = (3, 5, 15)``;
