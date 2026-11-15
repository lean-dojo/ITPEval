(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/coincidence_count_CoincidenceCountBag_coincidence_countqtvc: the
  coincidence-count loop invariant for two increasing integer lists, using
  recursively specified multisets of their suffixes. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory bagTheory;

val coincidence_count_CoincidenceCountBag_coincidence_count_vc =
  ``let cc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let cc_get =
      \xs : int list. \z : int.
        if cc_to_nat z < LENGTH xs then EL (cc_to_nat z) xs else 0
    in
    let cc_increasing =
      \xs : int list.
        !i j : int.
          0 <= i /\ i < j /\ j < &(LENGTH xs) ==>
          cc_get xs i <= cc_get xs j
    in
      !bagofsub : int list -> int -> int -> int bag.
        (!lo hi : int. !xs : int list.
           0 <= lo /\ lo <= hi /\ hi <= &(LENGTH xs) ==>
           if hi <= lo then
             bagofsub xs lo hi = EMPTY_BAG
           else
             bagofsub xs lo hi =
               BAG_INSERT (cc_get xs lo) (bagofsub xs (lo + 1) hi))
        ==>
        let bagof =
          \xs : int list. bagofsub xs 0 (&(LENGTH xs))
        in
        let drop =
          \xs : int list. \i : int. bagofsub xs i (&(LENGTH xs))
        in
          !a b : int list.
            cc_increasing a ==>
            cc_increasing b ==>
            0 <= (0 : int) /\
            0 <= &(LENGTH a) /\
            0 <= (0 : int) /\
            0 <= &(LENGTH b) /\
            0 +
                &(BAG_CARD
                    (BAG_INTER (drop a 0) (drop b 0))) =
              &(BAG_CARD
                  (BAG_INTER (bagof a) (bagof b))) /\
            !c j i : int.
              (0 <= i /\ i <= &(LENGTH a)) /\
              (0 <= j /\ j <= &(LENGTH b)) /\
              c +
                  &(BAG_CARD
                      (BAG_INTER (drop a i) (drop b j))) =
                &(BAG_CARD
                    (BAG_INTER (bagof a) (bagof b)))
              ==>
              !o1 : bool.
                (if i < &(LENGTH a) then
                   o1 =
                     (if j < &(LENGTH b) then T else F)
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
                        &(BAG_CARD
                            (BAG_INTER
                              (drop a (i + 1))
                              (drop b j))) =
                      &(BAG_CARD
                          (BAG_INTER (bagof a) (bagof b)))
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
                          &(BAG_CARD
                              (BAG_INTER
                                (drop a i)
                                (drop b (j + 1)))) =
                        &(BAG_CARD
                            (BAG_INTER (bagof a) (bagof b)))
                    else
                      (0 <= &(LENGTH a) - i + &(LENGTH b) - j /\
                       &(LENGTH a) - (i + 1) +
                           &(LENGTH b) - (j + 1) <
                         &(LENGTH a) - i + &(LENGTH b) - j) /\
                      (0 <= i + 1 /\ i + 1 <= &(LENGTH a)) /\
                      (0 <= j + 1 /\ j + 1 <= &(LENGTH b)) /\
                      c + 1 +
                          &(BAG_CARD
                              (BAG_INTER
                                (drop a (i + 1))
                                (drop b (j + 1)))) =
                        &(BAG_CARD
                            (BAG_INTER (bagof a) (bagof b)))
                else
                  c =
                    &(BAG_CARD
                        (BAG_INTER (bagof a) (bagof b)))``;
