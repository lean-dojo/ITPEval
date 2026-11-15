(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b2:
  the positive cardinalities of finite sets of vectors in real three-space
  that equal the set of all pairwise cross products are exactly 1 and 7.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val putnam_2022_b2 =
  ``let cross3 =
      \v w : (real # real) # real.
        ((SND (FST v) * SND w - SND v * SND (FST w),
          SND v * FST (FST w) - FST (FST v) * SND w),
         FST (FST v) * SND (FST w) -
           SND (FST v) * FST (FST w))
    in
      !n : num.
        (0 < n /\
         ?S : ((real # real) # real) set.
           FINITE S /\
           CARD S = n /\
           S =
             {u |
                ?v w : (real # real) # real.
                  v IN S /\ w IN S /\ u = cross3 v w})
        <=>
        n = 1 \/ n = 7``;
