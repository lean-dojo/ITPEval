(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_nextqtvc: the
  verification condition for computing the immediate lexicographic successor
  of an integer permutation by locating a pivot, swapping, and reversing the
  descending suffix. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val ntp4vc_lexperm_index_def = Define `
  ntp4vc_lexperm_index (i : int) =
    if i < (0 : int) then 0 else Num i`;

val ntp4vc_lexperm_nth_def = Define `
  ntp4vc_lexperm_nth (s : int list) (i : int) =
    if ntp4vc_lexperm_index i < LENGTH s
    then EL (ntp4vc_lexperm_index i) s
    else (0 : int)`;

val ntp4vc_lexperm_occ_all_def = Define `
  ntp4vc_lexperm_occ_all (x : int) (s : int list) =
    &(LENGTH (FILTER (\y : int. y = x) s))`;

val ntp4vc_lexperm_is_permutation_def = Define `
  ntp4vc_lexperm_is_permutation (p : int list) (a : int list) <=>
    LENGTH p = LENGTH a /\
    (!x : int.
       ntp4vc_lexperm_occ_all x p =
       ntp4vc_lexperm_occ_all x a)`;

val ntp4vc_lexperm_lt_def = Define `
  ntp4vc_lexperm_lt (p : int list) (q : int list) <=>
    (LENGTH p = LENGTH q /\ (0 : int) < &(LENGTH q)) /\
    (?i : int.
       ((0 : int) <= i /\ i < &(LENGTH p)) /\
       (!j : int.
          (0 : int) <= j /\ j < i
          ==> ntp4vc_lexperm_nth p j =
              ntp4vc_lexperm_nth q j) /\
       ntp4vc_lexperm_nth p i < ntp4vc_lexperm_nth q i)`;

val ntp4vc_lexperm_descending_def = Define `
  ntp4vc_lexperm_descending (s : int list) (lo : int) (hi : int) <=>
    ((0 : int) <= lo /\ lo <= hi /\ hi <= &(LENGTH s)) /\
    (!i j : int.
       lo <= i /\ i <= j /\ j < hi
       ==> ntp4vc_lexperm_nth s j <= ntp4vc_lexperm_nth s i)`;

val verifythis_2021_lexicographic_permutations_1_Top_nextqtvc_statement =
  ``!a a0 : int list.
    LENGTH a = LENGTH a0
    ==>
    ntp4vc_lexperm_is_permutation a a0
    ==>
    let n = &(LENGTH a) in
    let o1 = n - (1 : int) in
    ((-(1 : int) <= o1 /\ o1 < n) /\
     ((o1 = -(1 : int) /\ n = (0 : int)) \/
      ((0 : int) <= o1 /\
       ntp4vc_lexperm_descending a o1 n))) /\
    (!i : int.
       ((-(1 : int) <= i /\ i < n) /\
        ((i = -(1 : int) /\ n = (0 : int)) \/
         ((0 : int) <= i /\
          ntp4vc_lexperm_descending a i n)))
       ==>
       (((0 : int) < i
         ==>
         ((0 : int) <= i /\ i < &(LENGTH a)) /\
         (let o2 = i - (1 : int) in
          (0 : int) <= o2 /\ o2 < &(LENGTH a))) /\
        (!o2 : bool.
           (if (0 : int) < i
            then
              o2 =
              (if ntp4vc_lexperm_nth a i <=
                  ntp4vc_lexperm_nth a (i - (1 : int))
               then T
               else F)
            else o2 = F)
           ==>
           if o2 = T then
             ((0 : int) <= i /\ i - (1 : int) < i) /\
             (-(1 : int) <= i - (1 : int) /\
              i - (1 : int) < n) /\
             (((i - (1 : int) = -(1 : int)) /\ n = (0 : int)) \/
              ((0 : int) <= i - (1 : int) /\
               ntp4vc_lexperm_descending
                 a (i - (1 : int)) n))
           else if i <= (0 : int) then
             ntp4vc_lexperm_is_permutation a a0 /\
             (!p : int list.
                ntp4vc_lexperm_is_permutation p a0
                ==> ~ntp4vc_lexperm_lt a p)
           else
             let i0 = i - (1 : int) in
             ((0 : int) <= i0 /\ i0 < &(LENGTH a)) /\
             (let x = ntp4vc_lexperm_nth a i0 in
              let o3 = n - (1 : int) in
              ((i <= o3 /\ o3 < n) /\
               (!k : int.
                  o3 < k /\ k < n
                  ==> ntp4vc_lexperm_nth a k <= x)) /\
              (!j : int.
                 ((i <= j /\ j < n) /\
                  (!k : int.
                     j < k /\ k < n
                     ==> ntp4vc_lexperm_nth a k <= x))
                 ==>
                 let o4 = i - (1 : int) in
                 ((0 : int) <= o4 /\ o4 < &(LENGTH a)) /\
                 ((0 : int) <= j /\ j < &(LENGTH a)) /\
                 if ntp4vc_lexperm_nth a j <=
                    ntp4vc_lexperm_nth a o4
                 then
                   ((0 : int) <= j /\ j - (1 : int) < j) /\
                   (i <= j - (1 : int) /\ j - (1 : int) < n) /\
                   (!k : int.
                      j - (1 : int) < k /\ k < n
                      ==> ntp4vc_lexperm_nth a k <= x)
                 else
                   ((0 : int) <= j /\ j < &(LENGTH a)) /\
                   (let z = ntp4vc_lexperm_nth a j in
                    let o5 = i - (1 : int) in
                    (((0 : int) <= o5 /\ o5 < &(LENGTH a)) /\
                     ((0 : int) <= j /\ j < &(LENGTH a))) /\
                    (!a1 : int list.
                       LENGTH a1 = LENGTH a
                       ==>
                       ntp4vc_lexperm_nth a1 o5 =
                         ntp4vc_lexperm_nth a j /\
                       ntp4vc_lexperm_nth a1 j =
                         ntp4vc_lexperm_nth a o5 /\
                       (!k : int.
                          (0 : int) <= k /\ k < &(LENGTH a1)
                          ==> ~(k = o5)
                          ==> ~(k = j)
                          ==> ntp4vc_lexperm_nth a1 k =
                              ntp4vc_lexperm_nth a k) /\
                       ntp4vc_lexperm_is_permutation a1 a
                       ==>
                       ((i0 < i /\
                         i0 < n - (1 : int) /\
                         n - (1 : int) < n) /\
                        ntp4vc_lexperm_is_permutation a1 a0 /\
                        (!k : int.
                           (0 : int) <= k /\ k < i0
                           ==> ntp4vc_lexperm_nth a1 k =
                               ntp4vc_lexperm_nth a k) /\
                        ntp4vc_lexperm_nth a1 i0 = z /\
                        i - i0 = n - (n - (1 : int)) /\
                        (!k : int.
                           (0 : int) < k /\ k < i - i0
                           ==> ntp4vc_lexperm_nth a1 (i0 + k) =
                               ntp4vc_lexperm_nth a1 (n - k) /\
                               ntp4vc_lexperm_nth a1 (n - k) =
                               ntp4vc_lexperm_nth a1 (i0 + k))) /\
                       (!j1 i1 : int.
                        !a2 : int list.
                          LENGTH a2 = LENGTH a1
                          ==>
                          ((i0 < i1 /\ i0 < j1 /\ j1 < n) /\
                           ntp4vc_lexperm_is_permutation a2 a0 /\
                           (!k : int.
                              (0 : int) <= k /\ k < i0
                              ==> ntp4vc_lexperm_nth a2 k =
                                  ntp4vc_lexperm_nth a k) /\
                           ntp4vc_lexperm_nth a2 i0 = z /\
                           i1 - i0 = n - j1 /\
                           (!k : int.
                              i1 <= k /\ k <= j1
                              ==> ntp4vc_lexperm_nth a2 k =
                                  ntp4vc_lexperm_nth a1 k) /\
                           (!k : int.
                              (0 : int) < k /\ k < i1 - i0
                              ==> ntp4vc_lexperm_nth a2 (i0 + k) =
                                  ntp4vc_lexperm_nth a1 (n - k) /\
                                  ntp4vc_lexperm_nth a2 (n - k) =
                                  ntp4vc_lexperm_nth a1 (i0 + k)))
                          ==>
                          if i1 < j1 then
                            (((0 : int) <= i1 /\
                              i1 < &(LENGTH a2)) /\
                             ((0 : int) <= j1 /\
                              j1 < &(LENGTH a2))) /\
                            (!a3 : int list.
                               LENGTH a3 = LENGTH a2
                               ==>
                               ntp4vc_lexperm_nth a3 i1 =
                                 ntp4vc_lexperm_nth a2 j1 /\
                               ntp4vc_lexperm_nth a3 j1 =
                                 ntp4vc_lexperm_nth a2 i1 /\
                               (!k : int.
                                  (0 : int) <= k /\
                                  k < &(LENGTH a3)
                                  ==> ~(k = i1)
                                  ==> ~(k = j1)
                                  ==> ntp4vc_lexperm_nth a3 k =
                                      ntp4vc_lexperm_nth a2 k) /\
                               ntp4vc_lexperm_is_permutation a3 a2
                               ==>
                               ((0 : int) <= j1 - i1 /\
                                j1 - (1 : int) - (i1 + (1 : int)) <
                                  j1 - i1) /\
                               (i0 < i1 + (1 : int) /\
                                i0 < j1 - (1 : int) /\
                                j1 - (1 : int) < n) /\
                               ntp4vc_lexperm_is_permutation a3 a0 /\
                               (!k : int.
                                  (0 : int) <= k /\ k < i0
                                  ==> ntp4vc_lexperm_nth a3 k =
                                      ntp4vc_lexperm_nth a k) /\
                               ntp4vc_lexperm_nth a3 i0 = z /\
                               i1 + (1 : int) - i0 =
                                 n - (j1 - (1 : int)) /\
                               (!k : int.
                                  i1 + (1 : int) <= k /\
                                  k <= j1 - (1 : int)
                                  ==> ntp4vc_lexperm_nth a3 k =
                                      ntp4vc_lexperm_nth a1 k) /\
                               (!k : int.
                                  (0 : int) < k /\
                                  k < i1 + (1 : int) - i0
                                  ==> ntp4vc_lexperm_nth
                                        a3 (i0 + k) =
                                      ntp4vc_lexperm_nth a1 (n - k) /\
                                      ntp4vc_lexperm_nth a3 (n - k) =
                                      ntp4vc_lexperm_nth
                                        a1 (i0 + k)))
                          else
                            (!p : int list.
                               ntp4vc_lexperm_is_permutation p a0 /\
                               ntp4vc_lexperm_lt a p /\
                               ntp4vc_lexperm_lt p a2
                               ==>
                               let a11 = a in
                               let v = ntp4vc_lexperm_nth p i0 in
                               if v = x then
                                 let o6 = n - (1 : int) in
                                 let o7 = i0 + (1 : int) in
                                 (o7 <= o6 + (1 : int)
                                  ==>
                                  (!k : int.
                                     i0 + (1 : int) <= k /\ k < o7
                                     ==> ntp4vc_lexperm_nth p k =
                                         ntp4vc_lexperm_nth a11 k) /\
                                  (!l : int.
                                     ((o7 <= l /\ l <= o6) /\
                                      (!k : int.
                                         i0 + (1 : int) <= k /\ k < l
                                         ==> ntp4vc_lexperm_nth p k =
                                             ntp4vc_lexperm_nth a11 k))
                                     ==>
                                     ntp4vc_lexperm_nth p l =
                                       ntp4vc_lexperm_nth a11 l /\
                                     (!k : int.
                                        i0 + (1 : int) <= k /\
                                        k < l + (1 : int)
                                        ==> ntp4vc_lexperm_nth p k =
                                            ntp4vc_lexperm_nth a11 k)) /\
                                  ~(!k : int.
                                      i0 + (1 : int) <= k /\
                                      k < o6 + (1 : int)
                                      ==> ntp4vc_lexperm_nth p k =
                                          ntp4vc_lexperm_nth a11 k)) /\
                                 ~(o6 + (1 : int) < o7)
                               else
                                 v = z /\
                                 (let a21 = a2 in
                                  (LENGTH a21 = LENGTH a2 /\
                                   (!i2 : int.
                                      (0 : int) <= i2 /\
                                      i2 < &(LENGTH a21)
                                      ==> ntp4vc_lexperm_nth a21 i2 =
                                          ntp4vc_lexperm_nth a2 i2))
                                  ==>
                                  let o6 = n - (1 : int) in
                                  let o7 = i0 + (1 : int) in
                                  (o7 <= o6 + (1 : int)
                                   ==>
                                   (!k : int.
                                      i0 + (1 : int) <= k /\ k < o7
                                      ==> ntp4vc_lexperm_nth p k =
                                          ntp4vc_lexperm_nth a21 k) /\
                                   (!l : int.
                                      ((o7 <= l /\ l <= o6) /\
                                       (!k : int.
                                          i0 + (1 : int) <= k /\ k < l
                                          ==> ntp4vc_lexperm_nth p k =
                                              ntp4vc_lexperm_nth a21 k))
                                      ==>
                                      ntp4vc_lexperm_nth p l =
                                        ntp4vc_lexperm_nth a21 l /\
                                      (!k : int.
                                         i0 + (1 : int) <= k /\
                                         k < l + (1 : int)
                                         ==> ntp4vc_lexperm_nth p k =
                                             ntp4vc_lexperm_nth a21 k)) /\
                                   ~(!k : int.
                                       i0 + (1 : int) <= k /\
                                       k < o6 + (1 : int)
                                       ==> ntp4vc_lexperm_nth p k =
                                           ntp4vc_lexperm_nth a21 k)) /\
                                  ~(o6 + (1 : int) < o7))) /\
                            ((!p : int list.
                                ~(ntp4vc_lexperm_is_permutation p a0 /\
                                  ntp4vc_lexperm_lt a p /\
                                  ntp4vc_lexperm_lt p a2))
                             ==>
                             ntp4vc_lexperm_is_permutation a2 a0 /\
                             ntp4vc_lexperm_lt a a2 /\
                             (!p : int list.
                                ntp4vc_lexperm_is_permutation p a0
                                ==>
                                ~(ntp4vc_lexperm_lt a p /\
                                  ntp4vc_lexperm_lt p a2)))))))))))``;
