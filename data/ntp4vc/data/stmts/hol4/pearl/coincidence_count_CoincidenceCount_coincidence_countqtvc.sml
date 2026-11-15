(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/coincidence_count_CoincidenceCount_coincidence_countqtvc: the
  coincidence-count loop invariant for two strictly increasing integer lists,
  using finite sets of their suffix elements. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pred_setTheory;

val coincidence_count_CoincidenceCount_coincidence_count_vc =
  ``let cc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let cc_get =
      \xs : int list. \z : int.
        if cc_to_nat z < LENGTH xs then EL (cc_to_nat z) xs else 0
    in
    let cc_setof =
      \xs : int list.
        IMAGE (cc_get xs)
          {i : int | 0 <= i /\ i < &(LENGTH xs)}
    in
    let cc_drop =
      \xs : int list. \n : int.
        IMAGE (cc_get xs)
          {i : int | n <= i /\ i < &(LENGTH xs)}
    in
    let cc_increasing =
      \xs : int list.
        !i j : int.
          0 <= i /\ i < j /\ j < &(LENGTH xs) ==>
          cc_get xs i < cc_get xs j
    in
    let cc =
      \a b : int list.
        &(CARD (cc_setof a INTER cc_setof b))
    in
      !a b : int list.
        cc_increasing a ==>
        cc_increasing b ==>
        0 <= (0 : int) /\
        0 <= &(LENGTH a) /\
        0 <= (0 : int) /\
        0 <= &(LENGTH b) /\
        0 + &(CARD (cc_drop a 0 INTER cc_drop b 0)) = cc a b /\
        !c j i : int.
          (0 <= i /\ i <= &(LENGTH a)) /\
          (0 <= j /\ j <= &(LENGTH b)) /\
          c + &(CARD (cc_drop a i INTER cc_drop b j)) = cc a b
          ==>
          !o1 : bool.
            (if i < &(LENGTH a) then
               o1 = (if j < &(LENGTH b) then T else F)
             else
               o1 = F)
            ==>
            if o1 = T then
              (0 <= j /\ j < &(LENGTH b)) /\
              (0 <= i /\ i < &(LENGTH a)) /\
              if cc_get a i < cc_get b j then
                (0 <= &(LENGTH a) - i + &(LENGTH b) - j /\
                 &(LENGTH a) - (i + 1) + &(LENGTH b) - j <
                   &(LENGTH a) - i + &(LENGTH b) - j) /\
                (0 <= i + 1 /\ i + 1 <= &(LENGTH a)) /\
                (0 <= j /\ j <= &(LENGTH b)) /\
                c +
                    &(CARD
                        (cc_drop a (i + 1) INTER cc_drop b j)) =
                  cc a b
              else
                (0 <= j /\ j < &(LENGTH b)) /\
                (0 <= i /\ i < &(LENGTH a)) /\
                if cc_get b j < cc_get a i then
                  (0 <= &(LENGTH a) - i + &(LENGTH b) - j /\
                   &(LENGTH a) - i + &(LENGTH b) - (j + 1) <
                     &(LENGTH a) - i + &(LENGTH b) - j) /\
                  (0 <= i /\ i <= &(LENGTH a)) /\
                  (0 <= j + 1 /\ j + 1 <= &(LENGTH b)) /\
                  c +
                      &(CARD
                          (cc_drop a i INTER cc_drop b (j + 1))) =
                    cc a b
                else
                  (0 <= &(LENGTH a) - i + &(LENGTH b) - j /\
                   &(LENGTH a) - (i + 1) +
                       &(LENGTH b) - (j + 1) <
                     &(LENGTH a) - i + &(LENGTH b) - j) /\
                  (0 <= i + 1 /\ i + 1 <= &(LENGTH a)) /\
                  (0 <= j + 1 /\ j + 1 <= &(LENGTH b)) /\
                  c + 1 +
                      &(CARD
                          (cc_drop a (i + 1) INTER
                           cc_drop b (j + 1))) =
                    cc a b
            else
              c = cc a b``;
