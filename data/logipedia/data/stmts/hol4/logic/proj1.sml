(*
  Statement-only formalization of the Logipedia corpus artifact logic.proj1
  (catalog title "logic.proj1"): projection of the first proposition from a
  conjunction, universally quantified over propositions A and B. This file
  contains no proof.
*)

open HolKernel Parse boolLib;

val logic_proj1 =
  ``!(A : bool) (B : bool). A /\ B ==> A``;
