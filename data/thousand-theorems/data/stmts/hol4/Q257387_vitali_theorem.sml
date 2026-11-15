(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q257387 (thousand-theorems__hol4__Q257387), "Vitali theorem": a set obtained
  by choosing one representative from each rational-difference equivalence
  class in the real interval [0,1] is not Lebesgue measurable. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory ratTheory realTheory real_of_ratTheory;
open measureTheory borelTheory;

val vitaliSet_not_measurable =
  ``let equivalent =
      \x y : real.
        0 <= x /\ x <= 1 /\
        0 <= y /\ y <= 1 /\
        ?q : rat. x - y = real_of_rat q
    in
    let representative =
      \x : real. @y : real. equivalent x y
    in
    let vitaliSet =
      IMAGE representative {x : real | 0 <= x /\ x <= 1}
    in
      ~(vitaliSet IN measurable_sets lborel)``;
