(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a3:
  divisibility modulo 7 for digit differences after two successive
  single-digit replacement relations on nine decimal digits. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1995_a3 =
  ``!(relation : (num -> int) -> (num -> int) -> bool).
    !(digits_to_num : (num -> int) -> int).
      digits_to_num =
        (\dig : num -> int.
           ITSET
             (\i acc. dig i * (10 : int) ** i + acc)
             (count 9)
             (0 : int)) /\
      (!d e : num -> int.
         relation d e <=>
           ((!i : num.
               i IN count 9
               ==>
               d i < 10 /\ 0 <= d i /\
               e i < 10 /\ 0 <= e i) /\
            (!i : num.
               i IN count 9
               ==>
               (7 : int) int_divides
                 digits_to_num
                   (\j : num. if j = i then e j else d j))))
      ==>
      !d e f : num -> int.
        relation d e /\ relation e f
        ==>
        !i : num.
          i IN count 9
          ==>
          (7 : int) int_divides (d i - f i)``;
