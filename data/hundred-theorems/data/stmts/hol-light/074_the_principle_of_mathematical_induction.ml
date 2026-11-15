(*
  Statement-only formalization of "The Principle of Mathematical Induction" from Hundred
  Theorems item 074. This file contains no proof.
*)

`!P:num->bool.
   P 0 /\ (!n. P n ==> P (SUC n))
   ==> !n. P n`;;
