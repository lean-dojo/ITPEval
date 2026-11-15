(*
  Statement-only formalization of the Logipedia corpus artifact nat.eqb_n_n
  (catalog title "nat.eqb_n_n"): the Boolean equality test on any natural
  number and itself returns true. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_nat_eqb_def = Define `
  (logipedia_nat_eqb 0 0 = T) /\
  (logipedia_nat_eqb 0 (SUC m) = F) /\
  (logipedia_nat_eqb (SUC n) 0 = F) /\
  (logipedia_nat_eqb (SUC n) (SUC m) =
     logipedia_nat_eqb n m)`;

val nat_eqb_n_n =
  ``!n : num. logipedia_nat_eqb n n = T``;
