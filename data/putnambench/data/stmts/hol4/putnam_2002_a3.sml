(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a3:
  parity of the number of nonempty subsets of the first n positive integers
  whose arithmetic mean is an integer. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory;

val putnam_2002_a3 =
  ``!n Tn : int.
      2 <= n /\
      Tn =
        int_of_num
          (CARD
             {s : int set |
                s SUBSET {i : int | 1 <= i /\ i <= n} /\
                s <> {} /\
                int_of_num (CARD s) int_divides
                  ITSET (\i acc. i + acc) s (0 : int)})
      ==>
      (2 : int) int_divides (Tn - n)``;
