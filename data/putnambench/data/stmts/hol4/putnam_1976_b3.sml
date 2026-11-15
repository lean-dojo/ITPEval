(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1976_b3:
  a recurrence-controlled lower bound for the probability of intersecting
  locally dependent high-probability events. Nonadjacent events are pairwise
  independent, as in the published problem. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;
open extrealTheory sigma_algebraTheory measureTheory probabilityTheory;

val putnam_1976_b3 =
  ``!(p : 'a p_space) (n : num) (a : real)
     (u : num -> real) (E : num -> 'a set).
      prob_space p /\
      1 <= n /\
      0 <= a /\ a < 1 / 4 /\
      u 0 = 1 /\ u 1 = 1 - a /\
      (!k. 1 <= k ==>
           u (k + 1) = u k - a * u (k - 1)) /\
      (!k. 0 < u k) /\
      (!i. i < n ==> E i IN events p) /\
      (!i. i < n ==> Normal (1 - a) <= prob p (E i)) /\
      (!i j.
         i < n /\ j < n /\ (i + 1 < j \/ j + 1 < i)
         ==>
         indep p (E i) (E j))
      ==>
      Normal (u n) <=
      prob p (BIGINTER (IMAGE E (count n)))``;
