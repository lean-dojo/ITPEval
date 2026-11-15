(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b4:
  the number of sign-pattern regions cut out on the unit sphere by finitely
  many distinct great circles in general position. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val putnam_1964_b4 =
  ``let sphere3 =
      \x : (real # real) # real.
        FST (FST x) * FST (FST x) +
        SND (FST x) * SND (FST x) +
        SND x * SND x = 1
    in
      let dot3 =
        \u : (real # real) # real.
        \x : (real # real) # real.
          FST (FST u) * FST (FST x) +
          SND (FST u) * SND (FST x) +
          SND u * SND x
      in
        let solution = \n : num. n * n - n + 2
        in
          !n : num.
          !C : num -> ((real # real) # real -> bool).
          !v : num -> (real # real) # real.
          !IsRegion : ((real # real) # real -> bool) -> bool.
            0 < n /\
            (!i : num.
               i < n
               ==>
               C i =
                 \x : (real # real) # real.
                   sphere3 x /\ dot3 (v i) x = 0) /\
            (!i : num. i < n ==> v i <> ((0, 0), 0)) /\
            (!i j : num.
               i < n /\ j < n /\ C i = C j ==> i = j) /\
            (!x y : (real # real) # real.
               sphere3 x /\ sphere3 y
               ==>
               CARD {i : num | i < n /\ C i x /\ C i y} <= 2) /\
            (!R : (real # real) # real -> bool.
               IsRegion R <=>
               (?x : (real # real) # real. R x) /\
               ?sign : num -> real.
                 (!i : num.
                    i < n
                    ==>
                    sign i <> 0 /\
                    (sign i = 1 \/ sign i = -1)) /\
                 R =
                   \x : (real # real) # real.
                     sphere3 x /\
                     !i : num.
                       i < n ==> sgn (dot3 (v i) x) = sign i)
            ==>
            (if FINITE
                  {R : (real # real) # real -> bool | IsRegion R}
             then CARD {R : (real # real) # real -> bool | IsRegion R}
             else 0) =
            solution n``;
