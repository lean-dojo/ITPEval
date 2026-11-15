(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_O_n_elim (catalog title "nat.lt_O_n_elim"): every positive natural
  number satisfies any predicate that holds of every successor. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_O_n_elim =
  ``!n : num.
      0 < n ==>
      !P : num -> bool.
        (!m : num. P (SUC m)) ==>
        P n``;
