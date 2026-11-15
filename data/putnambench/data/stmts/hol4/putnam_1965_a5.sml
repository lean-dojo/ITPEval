(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a5:
  the number of orderings of 1 through n in which every entry after the
  first differs by one from an earlier entry is 2^(n - 1). This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1965_a5 =
  ``!n : num.
      0 < n
      ==>
      let entries = {m : num | 1 <= m /\ m <= n}
      in
        CARD
          {p : num -> num |
             BIJ p entries entries /\
             (!x : num. x NOTIN entries ==> p x = x) /\
             (!m : num.
                2 <= m /\ m <= n
                ==>
                ?k : num.
                  1 <= k /\ k < m /\
                  (p m = p k + 1 \/ p k = p m + 1))} =
        2 EXP (n - 1)``;
