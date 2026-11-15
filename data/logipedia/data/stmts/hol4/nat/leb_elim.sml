(*
  Statement-only formalization of the Logipedia corpus artifact nat.leb_elim
  (catalog title "nat.leb_elim"): for natural numbers n and m and a predicate
  P on Booleans, the true branch under n <= m and the false branch under its
  negation yield P at the Boolean comparison leb n m. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_nat_leb_def = Define `
  (logipedia_nat_leb 0 m = T) /\
  (logipedia_nat_leb (SUC n) 0 = F) /\
  (logipedia_nat_leb (SUC n) (SUC m) =
     logipedia_nat_leb n m)
`;

val nat_leb_elim =
  ``!(n : num) (m : num) (P : bool -> bool).
      ((n <= m) ==> P T) ==>
      (~(n <= m) ==> P F) ==>
      P (logipedia_nat_leb n m)``;
