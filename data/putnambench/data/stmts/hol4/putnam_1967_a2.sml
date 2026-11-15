(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a2:
  the recurrence and real exponential generating function for the number of
  symmetric nonnegative-integer matrices whose column sums are one. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     real_sigmaTheory seqTheory transcTheory;

val putnam_1967_a2 =
  ``!S : num -> int.
      S 0 = 1 /\
      (!n : num.
         1 <= n
         ==>
         S n =
           int_of_num
             (CARD
                {A : num -> num -> num |
                   (!i j : num.
                      i < n /\ j < n
                      ==>
                      A i j = A j i) /\
                   (!j : num.
                      j < n
                      ==>
                      SIGMA (\i : num. A i j) (count n) = 1) /\
                   (!i j : num.
                      n <= i \/ n <= j
                      ==>
                      A i j = 0)}))
      ==>
      ((!n : num.
          1 <= n
          ==>
          S (n + 1) =
            S n + int_of_num n * S (n - 1)) /\
       (!x : real.
          suminf
            (\n : num.
               real_of_int (S n) *
               (x pow n / &(FACT n))) =
          exp (x + x pow 2 / 2)))``;
