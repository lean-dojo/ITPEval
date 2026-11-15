(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a5:
  area-definiteness of coefficients for every configuration of finitely many
  planar points implies area-definiteness for spatial points. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory transcTheory;

val putnam_2013_a5 =
  ``let area2 =
      \A B C : real # real.
        abs
          ((FST B - FST A) * (SND C - SND A) -
           (SND B - SND A) * (FST C - FST A)) / 2
    in
    let area3 =
      \A B C : (real # real) # real.
        sqrt
          (((SND (FST B) - SND (FST A)) * (SND C - SND A) -
            (SND B - SND A) * (SND (FST C) - SND (FST A))) pow 2 +
           ((SND B - SND A) * (FST (FST C) - FST (FST A)) -
            (FST (FST B) - FST (FST A)) * (SND C - SND A)) pow 2 +
           ((FST (FST B) - FST (FST A)) *
              (SND (FST C) - SND (FST A)) -
            (SND (FST B) - SND (FST A)) *
              (FST (FST C) - FST (FST A))) pow 2) / 2
    in
      !m : num.
        3 <= m
        ==>
        !a : num -> num -> num -> real.
          (!A : num -> real # real.
             0 <=
               SIGMA
                 (\i : num.
                    SIGMA
                      (\j : num.
                         SIGMA
                           (\k : num.
                              if i < j /\ j < k
                              then a i j k * area2 (A i) (A j) (A k)
                              else 0)
                           (count m))
                      (count m))
                 (count m))
          ==>
          (!A : num -> (real # real) # real.
             0 <=
               SIGMA
                 (\i : num.
                    SIGMA
                      (\j : num.
                         SIGMA
                           (\k : num.
                              if i < j /\ j < k
                              then a i j k * area3 (A i) (A j) (A k)
                              else 0)
                           (count m))
                      (count m))
                 (count m))``;
