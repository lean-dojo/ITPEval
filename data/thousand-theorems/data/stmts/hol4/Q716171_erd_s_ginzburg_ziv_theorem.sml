(*
  Statement-only formalization of Thousand Theorems corpus artifact Q716171,
  "Erdős–Ginzburg–Ziv theorem": every finite indexed family of at least
  2 * n - 1 residue classes modulo n, represented by integers, contains an
  n-element subfamily whose sum is divisible by n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val q716171_int_sum_def = new_definition (
  "q716171_int_sum_def",
  ``q716171_int_sum (a : 'i -> int) (t : 'i set) =
      ITSET (\i acc. a i + acc) t 0``);

val erdos_ginzburg_ziv =
  ``!n : num. !s : 'i set. !a : 'i -> int.
      FINITE s /\ 2 * n - 1 <= CARD s
      ==>
      ?t : 'i set.
        FINITE t /\
        t SUBSET s /\
        CARD t = n /\
        int_of_num n int_divides q716171_int_sum a t``;
