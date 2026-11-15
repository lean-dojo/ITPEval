(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/skew_heaps_HeapSort_heapsortqtvc: the skew-heap heapsort
  verification condition, preserving heap order, element multiplicities,
  sorted prefixes, and permutation of the input list. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

Datatype:
  skew_heaps_tree =
    SkewHeapsEmpty
  | SkewHeapsNode skew_heaps_tree 'elt skew_heaps_tree
End

val skew_heaps_size_def = Define `
  (skew_heaps_size
      (SkewHeapsEmpty : 'elt skew_heaps_tree) = (0 : int)) /\
  (skew_heaps_size (SkewHeapsNode l x r) =
     (1 : int) + skew_heaps_size l + skew_heaps_size r)`;

val skew_heaps_occ_def = Define `
  (skew_heaps_occ x
      (SkewHeapsEmpty : 'elt skew_heaps_tree) = (0 : int)) /\
  (skew_heaps_occ x (SkewHeapsNode l y r) =
     (if y = x then (1 : int) else (0 : int)) +
       skew_heaps_occ x l + skew_heaps_occ x r)`;

val skew_heaps_mem_def = Define `
  skew_heaps_mem x t <=> (0 : int) < skew_heaps_occ x t`;

val skew_heaps_le_root_def = Define `
  (skew_heaps_le_root le e
      (SkewHeapsEmpty : 'elt skew_heaps_tree) = T) /\
  (skew_heaps_le_root le e (SkewHeapsNode l x r) = le e x)`;

val skew_heaps_heap_def = Define `
  (skew_heaps_heap le
      (SkewHeapsEmpty : 'elt skew_heaps_tree) = T) /\
  (skew_heaps_heap le (SkewHeapsNode l x r) =
     (skew_heaps_le_root le x l /\
      skew_heaps_heap le l /\
      skew_heaps_le_root le x r /\
      skew_heaps_heap le r))`;

val skew_heaps_minimum_def = Define `
  (skew_heaps_minimum
      (SkewHeapsEmpty : 'elt skew_heaps_tree) = ARB) /\
  (skew_heaps_minimum (SkewHeapsNode l x r) = x)`;

val skew_heaps_HeapSort_heapsort_vc =
  ``let vc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : 'elt list. \z : int.
        if z < 0 then
          ARB
        else if vc_to_nat z < LENGTH xs then
          EL (vc_to_nat z) xs
        else
          ARB
    in
    let vc_update =
      \xs : 'elt list. \z : int. \x : 'elt.
        LUPDATE x (vc_to_nat z) xs
    in
    let vc_map_occ =
      \x : 'elt. \xs : 'elt list. \lower upper : int.
        &(LENGTH
          (FILTER
            (\offset : num.
               vc_get xs (lower + &offset) = x)
            (GENLIST
              (\offset : num. offset)
              (if upper <= lower
               then 0
               else Num (upper - lower)))))
    in
    let vc_sorted_sub =
      \le : 'elt -> 'elt -> bool.
      \xs : 'elt list.
      \lower upper : int.
        !i1 i2 : int.
          lower <= i1 /\ i1 < i2 /\ i2 < upper ==>
          le (vc_get xs i1) (vc_get xs i2)
    in
    let vc_sorted =
      \le : 'elt -> 'elt -> bool.
      \xs : 'elt list.
        !i1 i2 : int.
          0 <= i1 /\ i1 < i2 /\ i2 < &(LENGTH xs) ==>
          le (vc_get xs i1) (vc_get xs i2)
    in
    let vc_second_loop =
      \le : 'elt -> 'elt -> bool.
      \original : 'elt list.
      \initial_heap : 'elt skew_heaps_tree.
      \n : int.
        let last = n - (1 : int)
        in
          (0 <= last + 1 ==>
           (vc_sorted_sub le original 0 0 /\
            (skew_heaps_heap le initial_heap /\
             skew_heaps_size initial_heap = n - 0) /\
            (!j : int.
               0 <= j /\ j < 0 ==>
               !e : 'elt.
                 skew_heaps_mem e initial_heap ==>
                 le (vc_get original j) e) /\
            (!e : 'elt.
               vc_map_occ e original 0 0 +
                 skew_heaps_occ e initial_heap =
               vc_map_occ e original 0 n)) /\
           !t : 'elt skew_heaps_tree.
           !current : 'elt list.
             LENGTH current = LENGTH original ==>
             (!i : int.
                ((0 <= i /\ i <= last) /\
                 vc_sorted_sub le current 0 i /\
                 (skew_heaps_heap le t /\
                  skew_heaps_size t = n - i) /\
                 (!j : int.
                    0 <= j /\ j < i ==>
                    !e : 'elt.
                      skew_heaps_mem e t ==>
                      le (vc_get current j) e) /\
                 (!e : 'elt.
                    vc_map_occ e current 0 i +
                      skew_heaps_occ e t =
                    vc_map_occ e original 0 n))
                ==>
                (skew_heaps_heap le t /\
                 0 < skew_heaps_size t) /\
                (let minimum = skew_heaps_minimum t
                 in
                   (0 <= i /\ i < &(LENGTH current)) /\
                   (LENGTH (vc_update current i minimum) =
                      LENGTH current ==>
                    (!k : int.
                       vc_get (vc_update current i minimum) k =
                         (if k = i then minimum
                          else vc_get current k)) ==>
                    (skew_heaps_heap le t /\
                     0 < skew_heaps_size t) /\
                    !t' : 'elt skew_heaps_tree.
                      skew_heaps_heap le t' /\
                      skew_heaps_occ (skew_heaps_minimum t) t' =
                        skew_heaps_occ (skew_heaps_minimum t) t - 1 /\
                      (!e : 'elt.
                         ~(e = skew_heaps_minimum t) ==>
                         skew_heaps_occ e t' =
                           skew_heaps_occ e t) /\
                      skew_heaps_size t' =
                        skew_heaps_size t - 1
                      ==>
                      vc_sorted_sub le
                        (vc_update current i minimum) 0 (i + 1) /\
                      (skew_heaps_heap le t' /\
                       skew_heaps_size t' = n - (i + 1)) /\
                      (!j : int.
                         0 <= j /\ j < i + 1 ==>
                         !e : 'elt.
                           skew_heaps_mem e t' ==>
                           le
                             (vc_get
                               (vc_update current i minimum) j)
                             e) /\
                      (!e : 'elt.
                         vc_map_occ e
                           (vc_update current i minimum) 0 (i + 1) +
                           skew_heaps_occ e t' =
                         vc_map_occ e original 0 n)))) /\
              ((vc_sorted_sub le current 0 (last + 1) /\
                (skew_heaps_heap le t /\
                 skew_heaps_size t = n - (last + 1)) /\
                (!j : int.
                   0 <= j /\ j < last + 1 ==>
                   !e : 'elt.
                     skew_heaps_mem e t ==>
                     le (vc_get current j) e) /\
                (!e : 'elt.
                   vc_map_occ e current 0 (last + 1) +
                     skew_heaps_occ e t =
                   vc_map_occ e original 0 n))
               ==>
               vc_sorted le current /\ PERM original current)) /\
          (last + 1 < 0 ==>
           vc_sorted le original /\ PERM original original)
    in
      !le : 'elt -> 'elt -> bool.
        (!x : 'elt. le x x) /\
        (!x y z : 'elt. le x y /\ le y z ==> le x z) /\
        (!x y : 'elt. le x y \/ le y x)
        ==>
        !a : 'elt list.
          let n = &(LENGTH a)
          in
          let last = n - (1 : int)
          in
            (0 <= last + 1 ==>
             ((skew_heaps_heap le
                 (SkewHeapsEmpty : 'elt skew_heaps_tree) /\
               skew_heaps_size
                 (SkewHeapsEmpty : 'elt skew_heaps_tree) = 0) /\
              (!e : 'elt.
                 vc_map_occ e a 0 n +
                   skew_heaps_occ e
                     (SkewHeapsEmpty : 'elt skew_heaps_tree) =
                 vc_map_occ e a 0 n)) /\
             !t : 'elt skew_heaps_tree.
               (((0 <= skew_heaps_size t /\
                  skew_heaps_size t <= last) /\
                 skew_heaps_heap le t /\
                 (!e : 'elt.
                    vc_map_occ e a (skew_heaps_size t) n +
                      skew_heaps_occ e t =
                    vc_map_occ e a 0 n))
                ==>
                (0 <= skew_heaps_size t /\
                 skew_heaps_size t < &(LENGTH a)) /\
                (let next = vc_get a (skew_heaps_size t)
                 in
                   skew_heaps_heap le t /\
                   !t' : 'elt skew_heaps_tree.
                     skew_heaps_heap le t' /\
                     skew_heaps_occ next t' =
                       skew_heaps_occ next t + 1 /\
                     (!e : 'elt.
                        ~(e = next) ==>
                        skew_heaps_occ e t' =
                          skew_heaps_occ e t) /\
                     skew_heaps_size t' =
                       skew_heaps_size t + 1
                     ==>
                     (skew_heaps_heap le t' /\
                      skew_heaps_size t' =
                        skew_heaps_size t + 1) /\
                     (!e : 'elt.
                        vc_map_occ e a
                            (skew_heaps_size t + 1) n +
                          skew_heaps_occ e t' =
                        vc_map_occ e a 0 n))) /\
               (((skew_heaps_heap le t /\
                  skew_heaps_size t = last + 1) /\
                 (!e : 'elt.
                    vc_map_occ e a (last + 1) n +
                      skew_heaps_occ e t =
                    vc_map_occ e a 0 n))
                ==>
                vc_second_loop le a t n)) /\
            (last + 1 < 0 ==>
             vc_second_loop le a
               (SkewHeapsEmpty : 'elt skew_heaps_tree) n)``;
