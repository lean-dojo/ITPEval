(*
  Statement-only formalization of the Logipedia corpus artifact logic.proj2
  (catalog title "logic.proj2"): projection of the second proposition from a
  conjunction, universally quantified over propositions A and B. This file
  contains no proof.
*)

open HolKernel Parse boolLib;

val logic_proj2 =
  ``!(A : bool) (B : bool). A /\ B ==> B``;
