(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a6:
  the number of ordered pairs of subsets of {1,...,10} whose elements exceed
  the cardinality of the other subset is 17711. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val putnam_1990_a6 =
  ``CARD
      {p : (num set # num set) |
         FST p SUBSET IMAGE SUC (count 10) /\
         SND p SUBSET IMAGE SUC (count 10) /\
         (!s : num. s IN FST p ==> CARD (SND p) < s) /\
         (!t : num. t IN SND p ==> CARD (FST p) < t)} =
    17711``;
