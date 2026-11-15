(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/decrease1_Decrease1_searchqtvc: an iterative search verification
  condition for finding the first zero in an integer list whose adjacent
  values may decrease by at most one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val decrease1_Decrease1_search_vc =
  ``let dec_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let dec_get =
      \xs : int list. \z : int.
        if dec_to_nat z < LENGTH xs then EL (dec_to_nat z) xs else 0
    in
    let decrease1 =
      \xs : int list.
        !k : int.
          0 <= k /\ k < &(LENGTH xs) - 1 ==>
          dec_get xs k - 1 <= dec_get xs (k + 1)
    in
      !a : int list.
        decrease1 a ==>
        (0 : int) <= 0 /\
        (!j : int.
           0 <= j /\ j < 0 ==>
           j < &(LENGTH a) ==>
           ~(dec_get a j = 0)) /\
        (!i : int.
           0 <= i /\
           (!j : int.
              0 <= j /\ j < i ==>
              j < &(LENGTH a) ==>
              ~(dec_get a j = 0)) ==>
           if i < &(LENGTH a) then
             (0 <= i /\ i < &(LENGTH a)) /\
             (if dec_get a i = 0 then
                (i = ~1 /\
                 !j : int.
                   0 <= j /\ j < &(LENGTH a) ==>
                   ~(dec_get a j = 0)) \/
                ((0 <= i /\ i < &(LENGTH a)) /\
                 dec_get a i = 0 /\
                 !j : int.
                   0 <= j /\ j < i ==>
                   ~(dec_get a j = 0))
              else
                (0 <= i /\ i < &(LENGTH a)) /\
                if 0 < dec_get a i then
                  (0 <= i /\ i < &(LENGTH a)) /\
                  (0 <= &(LENGTH a) - i /\
                   &(LENGTH a) - (i + dec_get a i) <
                     &(LENGTH a) - i) /\
                  0 <= i + dec_get a i /\
                  (!j : int.
                     0 <= j /\ j < i + dec_get a i ==>
                     j < &(LENGTH a) ==>
                     ~(dec_get a j = 0))
                else
                  (0 <= &(LENGTH a) - i /\
                   &(LENGTH a) - (i + 1) < &(LENGTH a) - i) /\
                  0 <= i + 1 /\
                  (!j : int.
                     0 <= j /\ j < i + 1 ==>
                     j < &(LENGTH a) ==>
                     ~(dec_get a j = 0)))
           else
             (!j : int.
                0 <= j /\ j < &(LENGTH a) ==>
                ~(dec_get a j = 0)) \/
             ((0 <= (~1 : int) /\ ~1 < &(LENGTH a)) /\
              dec_get a (~1) = 0 /\
              !j : int.
                0 <= j /\ j < ~1 ==>
                ~(dec_get a j = 0)))``;
