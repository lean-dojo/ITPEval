(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/decrease1_Decrease1_search_recqtvc: a recursive search verification
  condition for an integer list whose adjacent values may decrease by at most
  one, preserving the first-zero-or-no-zero postcondition and establishing
  termination of recursive calls. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val decrease1_Decrease1_search_rec_vc =
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
      !i : int.
        decrease1 a ==>
        0 <= i ==>
        let o1 = &(LENGTH a)
        in
          (i < o1 ==>
             (0 <= i /\ i < &(LENGTH a)) /\
             (~(dec_get a i = 0) ==>
                (0 <= i /\ i < &(LENGTH a)) /\
                if 0 < dec_get a i then
                  (0 <= i /\ i < &(LENGTH a)) /\
                  (let o2 = i + dec_get a i
                   in
                     (0 <= &(LENGTH a) - i /\
                      &(LENGTH a) - o2 < &(LENGTH a) - i) /\
                     decrease1 a /\
                     0 <= o2)
                else
                  let o2 = i + 1
                  in
                    (0 <= &(LENGTH a) - i /\
                     &(LENGTH a) - o2 < &(LENGTH a) - i) /\
                    decrease1 a /\
                    0 <= o2)) /\
          (!result : int.
             (if i < o1 then
                if dec_get a i = 0 then
                  result = i
                else if 0 < dec_get a i then
                  let o2 = i + dec_get a i
                  in
                    (result = ~1 /\
                     !j : int.
                       o2 <= j /\ j < &(LENGTH a) ==>
                       ~(dec_get a j = 0)) \/
                    ((o2 <= result /\ result < &(LENGTH a)) /\
                     dec_get a result = 0 /\
                     !j : int.
                       o2 <= j /\ j < result ==>
                       ~(dec_get a j = 0))
                else
                  let o2 = i + 1
                  in
                    (result = ~1 /\
                     !j : int.
                       o2 <= j /\ j < &(LENGTH a) ==>
                       ~(dec_get a j = 0)) \/
                    ((o2 <= result /\ result < &(LENGTH a)) /\
                     dec_get a result = 0 /\
                     !j : int.
                       o2 <= j /\ j < result ==>
                       ~(dec_get a j = 0))
              else
                result = ~1) ==>
             (result = ~1 /\
              !j : int.
                i <= j /\ j < &(LENGTH a) ==>
                ~(dec_get a j = 0)) \/
             ((i <= result /\ result < &(LENGTH a)) /\
              dec_get a result = 0 /\
              !j : int.
                i <= j /\ j < result ==>
                ~(dec_get a j = 0)))``;
