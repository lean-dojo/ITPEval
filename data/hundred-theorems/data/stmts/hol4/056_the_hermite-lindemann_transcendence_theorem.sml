(*
  Statement-only formalization of Hundred Theorems artifact 056, "The Hermite-Lindemann
  Transcendence Theorem": the complex exponential of a nonzero algebraic complex number is
  transcendental. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory realTheory intrealTheory complexTheory;

val hermite_lindemann_transcendence_theorem =
  ``!x : complex.
      let algebraic =
        \z : complex.
          ?coeffs : int list.
            (?a. MEM a coeffs /\ a <> 0) /\
            FOLDR
              (\a acc. complex_of_real (real_of_int a) + z * acc)
              0 coeffs = 0
      in
        algebraic x /\ x <> 0 ==>
        ~algebraic (complex_exp x)``;
