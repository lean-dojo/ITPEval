(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p8: the parity at indices
  2021, 2022, and 2023 of a natural-number sequence defined by a three-step recurrence. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_theory "hello";

val amc12a_2021_p8 =
  ``!d : num -> num.
      d 0 = 0 /\
      d 1 = 0 /\
      d 2 = 1 /\
      (!n : num. 3 <= n ==> d n = d (n - 1) + d (n - 3))
      ==>
      EVEN (d 2021) /\ ODD (d 2022) /\ EVEN (d 2023)``;

val _ = export_theory();
