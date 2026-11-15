(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_parityqtvc: initialization, preservation, and exit of
  a parity loop invariant over integers with inductively generated evenness.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val (sf_parity_even_rules,
     sf_parity_even_ind,
     sf_parity_even_cases) =
  Hol_reln `
    sf_parity_even (0 : int) /\
    (!x : int.
       sf_parity_even x ==>
       sf_parity_even (x + (2 : int)))
  `;

val sf_HoareLogic_parity_vc =
  ``!x : int.
      (0 : int) <= x ==>
      (0 : int) <= x /\
      (sf_parity_even (x - x) \/
       (0 : int) = (1 : int) /\
       sf_parity_even (x - x + (1 : int))) /\
      !y x1 : int.
        (0 : int) <= x1 /\
        (y = (0 : int) /\ sf_parity_even (x - x1) \/
         y = (1 : int) /\ sf_parity_even (x - x1 + (1 : int))) ==>
        if ~(x1 = (0 : int)) then
          ((0 : int) <= x1 /\ x1 - (1 : int) < x1) /\
          (0 : int) <= x1 - (1 : int) /\
          ((1 : int) - y = (0 : int) /\
           sf_parity_even (x - (x1 - (1 : int))) \/
           (1 : int) - y = (1 : int) /\
           sf_parity_even (x - (x1 - (1 : int)) + (1 : int)))
        else
          (y = (0 : int) <=> sf_parity_even x)``;
