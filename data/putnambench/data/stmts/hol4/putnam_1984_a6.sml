(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_a6:
  the last nonzero decimal digit of a factorial at sums of distinct powers of
  five depends only on the exponent sum, and the resulting function has least
  positive period four from index one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1984_a6 =
  ``!f : num -> num.
      (!n : num.
         ?z m : num.
           FACT n = 10 EXP z * m /\
           ~(m MOD 10 = 0) /\
           f n = m MOD 10)
      ==>
      ?g : num -> num.
        (!k : num. !a : num -> num.
           0 < k /\ INJ a (count k) UNIV
           ==>
           f (SIGMA (\i : num. 5 EXP (a i)) (count k)) =
             g (SIGMA a (count k))) /\
        (!s : num. 1 <= s ==> g s = g (s + 4)) /\
        (!p : num.
           0 < p /\
           (!s : num. 1 <= s ==> g s = g (s + p))
           ==>
           4 <= p)``;
