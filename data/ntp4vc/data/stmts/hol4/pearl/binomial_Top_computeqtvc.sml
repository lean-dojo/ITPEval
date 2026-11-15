(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_Top_computeqtvc: a verification condition for iteratively
  computing a binomial coefficient from its recursive specification using
  exact Euclidean division. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val binomial_Top_compute_vc =
  ``!infix_sl comb : int -> int -> int.
      (!y x : int.
         ~(y = 0) ==>
         infix_sl x y = ediv x y) ==>
      (!k n : int.
         0 <= k /\ k <= n ==>
         if k = 0 \/ k = n then
           comb n k = 1
         else
           comb n k =
             comb (n - 1) k + comb (n - 1) (k - 1)) ==>
      (!k n : int.
         0 <= k /\ k <= n ==>
         1 <= comb n k) ==>
      !k n : int.
        0 <= k ==>
        k <= n ==>
        let k1 = if k <= n - k then k else n - k
        in
          (1 <= k1 + 1 ==>
           ((1 <= (1 : int) /\ 1 <= k1 + 1) /\
            (1 : int) = comb n (1 - 1)) /\
           (!r : int.
              (!i : int.
                 ((1 <= i /\ i <= k1) /\
                  (1 <= i /\ i <= k1 + 1) /\
                  r = comb n (i - 1)) ==>
                 ~(i = 0) /\
                 (1 <= i + 1 /\ i + 1 <= k1 + 1) /\
                 infix_sl (r * (n - i + 1)) i =
                   comb n (i + 1 - 1)) /\
              (((1 <= k1 + 1 /\ k1 + 1 <= k1 + 1) /\
                r = comb n (k1 + 1 - 1)) ==>
               r = comb n k))) /\
          (k1 + 1 < 1 ==> (1 : int) = comb n k)``;
