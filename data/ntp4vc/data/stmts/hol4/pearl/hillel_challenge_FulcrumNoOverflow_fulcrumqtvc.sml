(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/hillel_challenge_FulcrumNoOverflow_fulcrumqtvc: the fulcrum-search
  verification condition for 32-bit array indices and exact integer partial
  sums, including the accumulator overflow bounds and minimum-difference loop
  invariants. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory integer_wordTheory pred_setTheory wordsTheory;

val fulcrum_int32_in_bounds_def = Define `
  fulcrum_int32_in_bounds (x : int) <=>
    -(2147483648 : int) <= x /\ x <= (2147483647 : int)`;

val fulcrum_sum_def = Define `
  fulcrum_sum
      (elts : 'array -> int -> word32) (a : 'array) (l : int) (u : int) =
    ITSET (\i acc. acc + w2i (elts a i))
      {i : int | l <= i /\ i < u} (0 : int)`;

val fulcrum_diff_def = Define `
  fulcrum_diff
      (elts : 'array -> int -> word32)
      (length : 'array -> word32) (a : 'array) (i : int) =
    ABS
      (fulcrum_sum elts a (0 : int) i -
       fulcrum_sum elts a i (w2i (length a)))`;

val fulcrum_big_invariant_def = Define `
  fulcrum_big_invariant
      (q : 'big -> word32) (r : 'big -> word32)
      (v : 'big -> int) (self : 'big) <=>
    -(2147483648 : int) <= w2i (q self) /\
    w2i (q self) <= (2147483647 : int) /\
    (0 : int) <= w2i (r self) /\
    w2i (r self) <= (2147483647 : int) /\
    v self =
      w2i (q self) * (2147483648 : int) + w2i (r self)`;

val fulcrum_search_phase_def = Define `
  fulcrum_search_phase
      (q : 'big -> word32) (r : 'big -> word32) (v : 'big -> int)
      (elts : 'array -> int -> word32) (length : 'array -> word32)
      (a : 'array) (n : word32) (o2 : word32) <=>
    !bestd1 : 'big. !besti : word32. !left2 : 'big. !right2 : 'big.
      ((!i : word32.
          let i1 = w2i i in
          ((0 : int) <= i1 /\ i1 <= w2i o2) /\
          (55 : int) < (89 : int) /\
          v left2 = fulcrum_sum elts a (0 : int) i1 /\
          v right2 = fulcrum_sum elts a i1 (w2i n) /\
          ((0 : int) <= w2i besti /\ w2i besti <= i1) /\
          v bestd1 = fulcrum_diff elts length a (w2i besti) /\
          (!j : int.
             (0 : int) <= j /\ j <= i1
             ==> v bestd1 <= fulcrum_diff elts length a j)
          ==>
          ((0 : int) <= w2i i /\ w2i i < w2i (length a)) /\
          (let o3 = elts a (w2i i) in
           -(2147483648 : int) * (2147483648 : int) <=
             v left2 + w2i o3 /\
           v left2 + w2i o3 <=
             (2147483648 : int) * (2147483648 : int) - (1 : int) /\
           (!left3 : 'big.
              v left3 = v left2 + w2i o3
              ==>
              ((0 : int) <= w2i i /\ w2i i < w2i (length a)) /\
              (let o4 = elts a (w2i i) in
               -(2147483648 : int) * (2147483648 : int) <=
                 v right2 - w2i o4 /\
               v right2 - w2i o4 <=
                 (2147483648 : int) * (2147483648 : int) - (1 : int) /\
               (!right3 : 'big.
                  v right3 = v right2 - w2i o4
                  ==>
                  -(2147483648 : int) * (2147483648 : int) <=
                    ABS (v left3 - v right3) /\
                  ABS (v left3 - v right3) <=
                    (2147483648 : int) * (2147483648 : int) - (1 : int) /\
                  (!d : 'big.
                     v d = ABS (v left3 - v right3)
                     ==>
                     ((0 : int) <= v d /\ (0 : int) <= v bestd1) /\
                     (if v d < v bestd1 then
                        !bestd2 : 'big.
                          fulcrum_int32_in_bounds
                            (w2i i + (1 : int)) /\
                          (!o5 : word32.
                             w2i o5 = w2i i + (1 : int)
                             ==>
                             fulcrum_big_invariant q r v d /\
                             (v d = v bestd2 /\
                              r d = r bestd2 /\
                              q d = q bestd2
                              ==>
                              (55 : int) < (89 : int) /\
                              v left3 =
                                fulcrum_sum
                                  elts a (0 : int) (i1 + (1 : int)) /\
                              v right3 =
                                fulcrum_sum
                                  elts a (i1 + (1 : int)) (w2i n) /\
                              ((0 : int) <= w2i o5 /\
                               w2i o5 <= i1 + (1 : int)) /\
                              v bestd2 =
                                fulcrum_diff
                                  elts length a (w2i o5) /\
                              (!j : int.
                                 (0 : int) <= j /\
                                 j <= i1 + (1 : int)
                                 ==>
                                 v bestd2 <=
                                   fulcrum_diff elts length a j)))
                      else
                        (55 : int) < (89 : int) /\
                        v left3 =
                          fulcrum_sum
                            elts a (0 : int) (i1 + (1 : int)) /\
                        v right3 =
                          fulcrum_sum
                            elts a (i1 + (1 : int)) (w2i n) /\
                        ((0 : int) <= w2i besti /\
                         w2i besti <= i1 + (1 : int)) /\
                        v bestd1 =
                          fulcrum_diff elts length a (w2i besti) /\
                        (!j : int.
                           (0 : int) <= j /\ j <= i1 + (1 : int)
                           ==>
                           v bestd1 <=
                             fulcrum_diff elts length a j)))))))) /\
       (((55 : int) < (89 : int) /\
         v left2 =
           fulcrum_sum elts a (0 : int) (w2i o2 + (1 : int)) /\
         v right2 =
           fulcrum_sum elts a (w2i o2 + (1 : int)) (w2i n) /\
         ((0 : int) <= w2i besti /\
          w2i besti <= w2i o2 + (1 : int)) /\
         v bestd1 = fulcrum_diff elts length a (w2i besti) /\
         (!j : int.
            (0 : int) <= j /\ j <= w2i o2 + (1 : int)
            ==> v bestd1 <= fulcrum_diff elts length a j))
        ==>
        ((0 : int) <= w2i besti /\
         w2i besti <= w2i (length a)) /\
        (!i : int.
           (0 : int) <= i /\ i <= w2i (length a)
           ==>
           fulcrum_diff elts length a (w2i besti) <=
             fulcrum_diff elts length a i)))`;

val fulcrum_after_right_def = Define `
  fulcrum_after_right
      (q : 'big -> word32) (r : 'big -> word32) (v : 'big -> int)
      (zero : 'big) (elts : 'array -> int -> word32)
      (length : 'array -> word32) (a : 'array) (n : word32)
      (right : 'big) <=>
    let left1 = zero in
    -(2147483648 : int) * (2147483648 : int) <=
      ABS (v left1 - v right) /\
    ABS (v left1 - v right) <=
      (2147483648 : int) * (2147483648 : int) - (1 : int) /\
    (!bestd : 'big.
       v bestd = ABS (v left1 - v right)
       ==>
       fulcrum_int32_in_bounds (w2i n - (1 : int)) /\
       (!o2 : word32.
          w2i o2 = w2i n - (1 : int)
          ==>
          ((((0 : int) <= w2i o2 + (1 : int))
            ==>
            ((55 : int) < (89 : int) /\
             v left1 = fulcrum_sum elts a (0 : int) (0 : int) /\
             v right = fulcrum_sum elts a (0 : int) (w2i n) /\
             (0 : int) <= (0 : int) /\
             v bestd = fulcrum_diff elts length a (0 : int) /\
             (!j : int.
                (0 : int) <= j /\ j <= (0 : int)
                ==> v bestd <= fulcrum_diff elts length a j)) /\
            fulcrum_search_phase q r v elts length a n o2) /\
           (w2i o2 + (1 : int) < (0 : int)
            ==>
            (((0 : int) <= (0 : int) /\
              (0 : int) <= w2i (length a)) /\
             (!i : int.
                (0 : int) <= i /\ i <= w2i (length a)
                ==> fulcrum_diff elts length a (0 : int) <=
                    fulcrum_diff elts length a i))))))`;

val hillel_challenge_FulcrumNoOverflow_fulcrumqtvc =
  ``!q : 'big -> word32.
    !r : 'big -> word32.
    !v : 'big -> int.
    !zero : 'big.
    !elts : 'array -> int -> word32.
    !length : 'array -> word32.
      ((!self : 'big. fulcrum_big_invariant q r v self) /\
       (!x y : 'big.
          q x = q y /\ r x = r y /\ v x = v y ==> x = y) /\
       q zero = (0w : word32) /\
       r zero = (0w : word32) /\
       v zero = (0 : int))
      ==>
      !a : 'array.
        w2i (length a) < (2147483647 : int)
        ==>
        let n = length a in
        let right1 = zero in
        fulcrum_int32_in_bounds (w2i n - (1 : int)) /\
        (!o1 : word32.
           w2i o1 = w2i n - (1 : int)
           ==>
           ((((0 : int) <= w2i o1 + (1 : int))
             ==>
             ((55 : int) < (89 : int) /\
              v right1 =
                fulcrum_sum elts a (0 : int) (0 : int)) /\
             (!right2 : 'big.
                ((!i : word32.
                    let i1 = w2i i in
                    ((0 : int) <= i1 /\ i1 <= w2i o1) /\
                    (55 : int) < (89 : int) /\
                    v right2 =
                      fulcrum_sum elts a (0 : int) i1
                    ==>
                    ((0 : int) <= w2i i /\
                     w2i i < w2i (length a)) /\
                    (let o2 = elts a (w2i i) in
                     -(2147483648 : int) * (2147483648 : int) <=
                       v right2 + w2i o2 /\
                     v right2 + w2i o2 <=
                       (2147483648 : int) * (2147483648 : int) -
                       (1 : int) /\
                     (!right3 : 'big.
                        v right3 = v right2 + w2i o2
                        ==>
                        (55 : int) < (89 : int) /\
                        v right3 =
                          fulcrum_sum
                            elts a (0 : int) (i1 + (1 : int))))) /\
                 (((55 : int) < (89 : int) /\
                   v right2 =
                     fulcrum_sum
                       elts a (0 : int) (w2i o1 + (1 : int)))
                  ==>
                  fulcrum_after_right
                    q r v zero elts length a n right2))) /\
            (w2i o1 + (1 : int) < (0 : int)
             ==>
             fulcrum_after_right
               q r v zero elts length a n right1))))``;
