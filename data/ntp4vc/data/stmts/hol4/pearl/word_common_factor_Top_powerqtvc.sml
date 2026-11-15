(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/word_common_factor_Top_powerqtvc: the recursive word-power
  termination condition stating that a nonzero nonnegative integer exponent
  has a nonnegative predecessor strictly smaller than itself. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val word_common_factor_Top_powerqtvc_statement =
  ``!n : int.
      (0 : int) <= n ==>
      ~(n = (0 : int)) ==>
      let o1 = n - (1 : int)
      in
        (((0 : int) <= n /\ o1 < n) /\ (0 : int) <= o1)``;
