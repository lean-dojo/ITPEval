(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1457052, "Well-ordering theorem": every type admits a strict linear order
  that is well-founded. This file contains no proof.
*)

open HolKernel Parse boolLib;
open relationTheory;

val exists_wellOrder =
  ``?lt : 'a -> 'a -> bool. StrongLinearOrder lt /\ WF lt``;
