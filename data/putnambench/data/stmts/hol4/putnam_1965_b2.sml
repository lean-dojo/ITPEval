(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b2:
  equality of the sums of squared win and loss counts in a finite
  round-robin tournament. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1965_b2 =
  ``!n : num.
      !(won : 'a -> 'a -> bool) (w l : 'a -> int).
        FINITE (UNIV : 'a set) /\
        CARD (UNIV : 'a set) = n /\
        1 < n /\
        (!i : 'a. won i i = F) /\
        (!i j : 'a.
           i <> j
           ==>
           won i j = ~(won j i)) /\
        w =
          (\r : 'a.
             SIGMA
               (\j : 'a. if won r j then (1 : int) else 0)
               (UNIV : 'a set)) /\
        l =
          (\r : 'a.
             int_of_num n - 1 - w r)
        ==>
        SIGMA (\r : 'a. w r ** 2) (UNIV : 'a set) =
        SIGMA (\r : 'a. l r ** 2) (UNIV : 'a set)``;
