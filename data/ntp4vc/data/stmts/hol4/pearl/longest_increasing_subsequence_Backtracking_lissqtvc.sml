(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/longest_increasing_subsequence_Backtracking_lissqtvc: a backtracking
  verification condition for constructing a longest strictly increasing
  subsequence of a list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val lis_to_nat_def = Define `
  lis_to_nat (z : int) = if z < 0 then 0 else Num z`;

val lis_iget_def = Define `
  lis_iget (xs : int list) (z : int) =
    if lis_to_nat z < LENGTH xs then EL (lis_to_nat z) xs else (0 : int)`;

val lis_get_def = Define `
  lis_get (xs : 'a list) (z : int) =
    if lis_to_nat z < LENGTH xs then EL (lis_to_nat z) xs else ARB`;

val lis_ilen_def = Define `
  lis_ilen (xs : 'a list) = &(LENGTH xs)`;

val lis_strict_order_def = Define `
  lis_strict_order (lt : 'a -> 'a -> bool) <=>
    (!x y z. lt x y /\ lt y z ==> lt x z) /\
    (!x y. lt x y ==> ~lt y x) /\
    (!x y. lt x y \/ lt y x \/ x = y)`;

val lis_iss_def = Define `
  lis_iss (lt : 'a -> 'a -> bool) (s : int list) (w : 'a list) <=>
    (!i : int.
       (0 : int) <= i /\ i < lis_ilen s ==>
       (0 : int) <= lis_iget s i /\ lis_iget s i < lis_ilen w) /\
    (!i j : int.
       (0 : int) <= i /\ i < j /\ j < lis_ilen s ==>
       lis_iget s i < lis_iget s j /\
       lt (lis_get w (lis_iget s i)) (lis_get w (lis_iget s j)))`;

val lis_liss_def = Define `
  lis_liss (lt : 'a -> 'a -> bool) (s : int list) (w : 'a list) <=>
    lis_iss lt s w /\
    !s' : int list.
      lis_iss lt s' w ==> lis_ilen s' <= lis_ilen s`;

val lis_pair_opt_def = Define `
  lis_pair_opt
    (lt : 'a -> 'a -> bool) (w : 'a list)
    (first : int) (bound : int) (s : int list) <=>
      (0 : int) < lis_ilen s /\
      lis_iget s 0 = first /\
      lis_iss lt s w /\
      !s' : int list.
        lis_iss lt s' w ==>
        (2 : int) <= lis_ilen s' ==>
        lis_iget s' 0 = first /\
        first < lis_iget s' 1 /\
        lis_iget s' 1 < bound ==>
        lis_ilen s' <= lis_ilen s`;

val lis_start_opt_def = Define `
  lis_start_opt
    (lt : 'a -> 'a -> bool) (w : 'a list)
    (first : int) (s : int list) <=>
      (0 : int) < lis_ilen s /\
      lis_iget s 0 = first /\
      lis_iss lt s w /\
      !s' : int list.
        lis_iss lt s' w ==>
        (1 : int) <= lis_ilen s' ==>
        lis_iget s' 0 = first ==>
        lis_ilen s' <= lis_ilen s`;

val lis_prefix_opt_def = Define `
  lis_prefix_opt
    (lt : 'a -> 'a -> bool) (w : 'a list)
    (bound : int) (s : int list) <=>
      lis_iss lt s w /\
      !s' : int list.
        lis_iss lt s' w ==>
        (1 : int) <= lis_ilen s' ==>
        lis_iget s' 0 < bound ==>
        lis_ilen s' <= lis_ilen s`;

val lis_cons_shape_def = Define `
  lis_cons_shape (first : int) (tail : int list) (whole : int list) <=>
    lis_ilen whole = (1 : int) + lis_ilen tail /\
    lis_iget whole 0 = first /\
    !i : int.
      (0 : int) < i /\ i <= lis_ilen tail ==>
      lis_iget whole i = lis_iget tail (i - (1 : int))`;

val longest_increasing_subsequence_Backtracking_liss_vc =
  ``!lt : 'a -> 'a -> bool.
      lis_strict_order lt ==>
      !w : 'a list.
        ((!i : int.
            (0 : int) <= i /\ i < lis_ilen w ==>
            let o1 = [i] in
              lis_ilen o1 = (1 : int) /\ lis_iget o1 0 = i ==>
              let o2 = lis_ilen w - (1 : int) in
              let o3 = i + (1 : int) in
                ((o3 <= o2 + (1 : int) ==>
                   ((lis_ilen o1 = (1 : int) /\
                     lis_pair_opt lt w i o3 o1) /\
                    !s : int list. !len : int.
                      ((!j : int.
                          ((o3 <= j /\ j <= o2) /\
                           len = lis_ilen s /\
                           lis_pair_opt lt w i j s) ==>
                          if lt (lis_get w i) (lis_get w j) then
                            (((0 : int) <= lis_ilen w - i /\
                              lis_ilen w - j < lis_ilen w - i) /\
                             (0 : int) <= j /\ j < lis_ilen w) /\
                            (!sj : int list.
                               lis_start_opt lt w j sj ==>
                               if len < (1 : int) + lis_ilen sj then
                                 let o4 = i :: sj in
                                   lis_cons_shape i sj o4 ==>
                                   (lis_ilen o4 =
                                      (1 : int) + lis_ilen sj) /\
                                   lis_pair_opt
                                     lt w i (j + (1 : int)) o4
                               else
                                 len = lis_ilen s /\
                                 lis_pair_opt
                                   lt w i (j + (1 : int)) s)
                          else
                            len = lis_ilen s /\
                            lis_pair_opt
                              lt w i (j + (1 : int)) s) /\
                       (len = lis_ilen s /\
                        lis_pair_opt lt w i (o2 + (1 : int)) s ==>
                        len = lis_ilen s /\
                        lis_start_opt lt w i s))) /\
                 (o2 + (1 : int) < o3 ==>
                  lis_ilen o1 = (1 : int) /\
                  lis_start_opt lt w i o1)))) /\
         (let o1 = lis_ilen w - (1 : int) in
            (((0 : int) <= o1 + (1 : int) ==>
               ((lis_ilen ([] : int list) = (0 : int) /\
                 lis_prefix_opt lt w (0 : int) []) /\
                !s : int list. !len : int.
                  ((!i : int.
                      (((0 : int) <= i /\ i <= o1) /\
                       len = lis_ilen s /\
                       lis_prefix_opt lt w i s) ==>
                      (((0 : int) <= i /\ i < lis_ilen w) /\
                       !si : int list.
                         lis_start_opt lt w i si ==>
                         if len < lis_ilen si then
                           lis_prefix_opt lt w (i + (1 : int)) si
                         else
                           len = lis_ilen s /\
                           lis_prefix_opt
                             lt w (i + (1 : int)) s)) /\
                   (len = lis_ilen s /\
                    lis_prefix_opt lt w (o1 + (1 : int)) s ==>
                    len = lis_ilen s /\
                    lis_liss lt s w))) /\
             (o1 + (1 : int) < (0 : int) ==>
              lis_ilen ([] : int list) = (0 : int) /\
              lis_liss lt [] w)))))``;
