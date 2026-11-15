(*
  Statement-only formalization of miniF2F valid problem numbertheory_sqmod3in01d:
  every integer square has remainder 0 or 1 modulo 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val numbertheory_sqmod3in01d =
  ``!a : int.
      (a ** 2) % 3 = 0 \/
      (a ** 2) % 3 = 1``;
