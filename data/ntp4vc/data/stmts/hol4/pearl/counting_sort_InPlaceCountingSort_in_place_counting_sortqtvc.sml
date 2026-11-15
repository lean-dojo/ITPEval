(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/counting_sort_InPlaceCountingSort_in_place_counting_sortqtvc: an
  in-place counting-sort verification condition preserving count invariants,
  sorted prefixes, and permutation of the input integer list. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pred_setTheory;

val counting_sort_InPlaceCountingSort_in_place_counting_sort_vc =
  ``let cs_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let cs_get =
      \xs : int list. \z : int.
        if cs_to_nat z < LENGTH xs then EL (cs_to_nat z) xs else 0
    in
    let cs_numeq =
      \xs : int list. \v lower upper : int.
        &(CARD
            {n : int |
              lower <= n /\ n < upper /\ cs_get xs n = v})
    in
    let cs_numlt =
      \xs : int list. \v lower upper : int.
        &(CARD
            {n : int |
              lower <= n /\ n < upper /\ cs_get xs n < v})
    in
    let cs_sorted_sub =
      \xs : int list. \lower upper : int.
        !i1 i2 : int.
          lower <= i1 /\ i1 <= i2 /\ i2 < upper ==>
          cs_get xs i1 <= cs_get xs i2
    in
    let cs_sorted =
      \xs : int list. cs_sorted_sub xs 0 (&(LENGTH xs))
    in
    let cs_k_values =
      \k : int. \xs : int list.
        !i : int.
          0 <= i /\ i < &(LENGTH xs) ==>
          0 <= cs_get xs i /\ cs_get xs i < k
    in
    let cs_permut =
      \k : int. \xs ys : int list.
        LENGTH xs = LENGTH ys /\
        !v : int.
          0 <= v /\ v < k ==>
          cs_numeq xs v 0 (&(LENGTH xs)) =
            cs_numeq ys v 0 (&(LENGTH ys))
    in
      !k : int.
        0 < k ==>
        !a : int list.
          cs_k_values k a ==>
          let o1 = k in
            0 <= o1 /\
            !c : int list.
              ((!i : int.
                  0 <= i /\ i < o1 ==> cs_get c i = 0) /\
               &(LENGTH c) = o1) ==>
              let cs_finish =
                \counts : int list.
                  let o3 = k - 1 in
                    (0 <= o3 + 1 ==>
                       ((0 : int) =
                          cs_numlt a 0 0 (&(LENGTH a)) /\
                        cs_sorted_sub a 0 0 /\
                        (!e : int.
                           0 <= e /\ e < 0 ==>
                           0 <= cs_get a e /\ cs_get a e < 0) /\
                        (!f : int.
                           0 <= f /\ f < 0 ==>
                           cs_numeq a f 0 0 =
                             cs_numeq a f 0 (&(LENGTH a)))) /\
                       !j : int. !a1 : int list.
                         LENGTH a1 = LENGTH a ==>
                         ((!v : int.
                             ((0 <= v /\ v <= o3) /\
                              j =
                                cs_numlt a v 0 (&(LENGTH a1)) /\
                              cs_sorted_sub a1 0 j /\
                              (!e : int.
                                 0 <= e /\ e < j ==>
                                 0 <= cs_get a1 e /\
                                 cs_get a1 e < v) /\
                              (!f : int.
                                 0 <= f /\ f < v ==>
                                 cs_numeq a1 f 0 j =
                                   cs_numeq
                                     a f 0 (&(LENGTH a1)))) ==>
                             (0 <= v /\
                              v < &(LENGTH counts)) /\
                             let o4 = cs_get counts v in
                               (((1 <= o4 + 1 ==>
                                    (j - 1 + 1 =
                                       cs_numlt
                                         a v 0 (&(LENGTH a1)) /\
                                     cs_sorted_sub a1 0 j /\
                                     (!e : int.
                                        0 <= e /\ e < j ==>
                                        0 <= cs_get a1 e /\
                                        cs_get a1 e <= v) /\
                                     (!f : int.
                                        0 <= f /\ f < v ==>
                                        cs_numeq a1 f 0 j =
                                          cs_numeq
                                            a f 0 (&(LENGTH a1))) /\
                                     cs_numeq a1 v 0 j = 1 - 1)) /\
                                  !j1 : int. !a2 : int list.
                                    LENGTH a2 = LENGTH a1 ==>
                                    ((!i : int.
                                        ((1 <= i /\ i <= o4) /\
                                         j1 - i + 1 =
                                           cs_numlt
                                             a v 0
                                               (&(LENGTH a2)) /\
                                         cs_sorted_sub a2 0 j1 /\
                                         (!e : int.
                                            0 <= e /\ e < j1 ==>
                                            0 <= cs_get a2 e /\
                                            cs_get a2 e <= v) /\
                                         (!f : int.
                                            0 <= f /\ f < v ==>
                                            cs_numeq a2 f 0 j1 =
                                              cs_numeq
                                                a f 0
                                                  (&(LENGTH a2))) /\
                                         cs_numeq a2 v 0 j1 =
                                           i - 1) ==>
                                        (0 <= j1 /\
                                         j1 < &(LENGTH a2)) /\
                                        (LENGTH
                                           (LUPDATE
                                              v
                                              (cs_to_nat j1)
                                              a2) =
                                           LENGTH a2 ==>
                                         j1 + 1 - (i + 1) + 1 =
                                           cs_numlt
                                             a v 0
                                               (&(LENGTH
                                                   (LUPDATE
                                                      v
                                                      (cs_to_nat j1)
                                                      a2))) /\
                                         cs_sorted_sub
                                           (LUPDATE
                                              v
                                              (cs_to_nat j1)
                                              a2)
                                           0
                                           (j1 + 1) /\
                                         (!e : int.
                                            0 <= e /\ e < j1 + 1 ==>
                                            0 <=
                                              cs_get
                                                (LUPDATE
                                                   v
                                                   (cs_to_nat j1)
                                                   a2)
                                                e /\
                                            cs_get
                                              (LUPDATE
                                                 v
                                                 (cs_to_nat j1)
                                                 a2)
                                              e <= v) /\
                                         (!f : int.
                                            0 <= f /\ f < v ==>
                                            cs_numeq
                                              (LUPDATE
                                                 v
                                                 (cs_to_nat j1)
                                                 a2)
                                              f
                                              0
                                              (j1 + 1) =
                                            cs_numeq
                                              a f 0
                                                (&(LENGTH
                                                    (LUPDATE
                                                       v
                                                       (cs_to_nat j1)
                                                       a2)))) /\
                                         cs_numeq
                                           (LUPDATE
                                              v
                                              (cs_to_nat j1)
                                              a2)
                                           v
                                           0
                                           (j1 + 1) =
                                         i + 1 - 1)) /\
                                     ((j1 - (o4 + 1) + 1 =
                                         cs_numlt
                                           a v 0 (&(LENGTH a2)) /\
                                       cs_sorted_sub a2 0 j1 /\
                                       (!e : int.
                                          0 <= e /\ e < j1 ==>
                                          0 <= cs_get a2 e /\
                                          cs_get a2 e <= v) /\
                                       (!f : int.
                                          0 <= f /\ f < v ==>
                                          cs_numeq a2 f 0 j1 =
                                            cs_numeq
                                              a f 0 (&(LENGTH a2))) /\
                                       cs_numeq a2 v 0 j1 =
                                         o4 + 1 - 1) ==>
                                      j1 =
                                        cs_numlt
                                          a (v + 1) 0
                                            (&(LENGTH a2)) /\
                                      cs_sorted_sub a2 0 j1 /\
                                      (!e : int.
                                         0 <= e /\ e < j1 ==>
                                         0 <= cs_get a2 e /\
                                         cs_get a2 e < v + 1) /\
                                      (!f : int.
                                         0 <= f /\ f < v + 1 ==>
                                         cs_numeq a2 f 0 j1 =
                                           cs_numeq
                                             a f 0
                                               (&(LENGTH a2)))))) /\
                                (o4 + 1 < 1 ==>
                                   j =
                                     cs_numlt
                                       a (v + 1) 0
                                         (&(LENGTH a1)) /\
                                   cs_sorted_sub a1 0 j /\
                                   (!e : int.
                                      0 <= e /\ e < j ==>
                                      0 <= cs_get a1 e /\
                                      cs_get a1 e < v + 1) /\
                                   (!f : int.
                                      0 <= f /\ f < v + 1 ==>
                                      cs_numeq a1 f 0 j =
                                        cs_numeq
                                          a f 0
                                            (&(LENGTH a1)))))) /\
                          ((j =
                              cs_numlt
                                a (o3 + 1) 0 (&(LENGTH a1)) /\
                            cs_sorted_sub a1 0 j /\
                            (!e : int.
                               0 <= e /\ e < j ==>
                               0 <= cs_get a1 e /\
                               cs_get a1 e < o3 + 1) /\
                            (!f : int.
                               0 <= f /\ f < o3 + 1 ==>
                               cs_numeq a1 f 0 j =
                                 cs_numeq
                                   a f 0 (&(LENGTH a1)))) ==>
                           cs_sorted a1 /\
                           cs_permut k a a1)) /\
                    (o3 + 1 < 0 ==>
                       cs_sorted a /\ cs_permut k a a))
              in
              let o2 = &(LENGTH a) - 1 in
                (0 <= o2 + 1 ==>
                   (!v : int.
                      0 <= v /\ v < k ==>
                      cs_get c v = cs_numeq a v 0 0) /\
                   !c1 : int list.
                     LENGTH c1 = LENGTH c ==>
                     ((!i : int.
                         ((0 <= i /\ i <= o2) /\
                          (!v : int.
                             0 <= v /\ v < k ==>
                             cs_get c1 v =
                               cs_numeq a v 0 i)) ==>
                         (0 <= i /\ i < &(LENGTH a)) /\
                         let v = cs_get a i in
                           (0 <= v /\ v < &(LENGTH c1)) /\
                           let o3 = cs_get c1 v + 1 in
                             (0 <= v /\ v < &(LENGTH c1)) /\
                             (LENGTH
                                (LUPDATE
                                   o3
                                   (cs_to_nat v)
                                   c1) =
                                LENGTH c1 ==>
                              !v1 : int.
                                0 <= v1 /\ v1 < k ==>
                                cs_get
                                  (LUPDATE
                                     o3
                                     (cs_to_nat v)
                                     c1)
                                  v1 =
                                cs_numeq
                                  a v1 0 (i + 1))) /\
                      ((!v : int.
                          0 <= v /\ v < k ==>
                          cs_get c1 v =
                            cs_numeq a v 0 (o2 + 1)) ==>
                       cs_finish c1)) /\
                (o2 + 1 < 0 ==> cs_finish c))``;
