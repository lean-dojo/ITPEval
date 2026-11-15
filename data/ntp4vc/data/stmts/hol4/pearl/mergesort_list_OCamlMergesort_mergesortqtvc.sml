(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_mergesortqtvc: the list mergesort
  verification condition, preserving sortedness and permutation of the
  original list through a full-length prefix. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val mergesort_list_OCamlMergesort_mergesort_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (sorted : 'elt list -> bool)
      (prefix1 : int -> 'elt list -> 'elt list).
      (!x : 'elt. le x x) ==>
      (!x y z : 'elt. le x y /\ le y z ==> le x z) ==>
      (!x y : 'elt. le x y \/ le y x) ==>
      sorted [] ==>
      (!x : 'elt. sorted [x]) ==>
      (!x y : 'elt.
       !l : 'elt list.
         le x y ==>
         sorted (y::l) ==>
         sorted (x::y::l)) ==>
      (!l : 'elt list.
       !x : 'elt.
         ((!y : 'elt. MEM y l ==> le x y) /\ sorted l) <=>
         sorted (x::l)) ==>
      (!l1 l2 : 'elt list.
         (sorted l1 /\
          sorted l2 /\
          (!x y : 'elt.
             MEM x l1 ==>
             MEM y l2 ==>
             le x y)) <=>
         sorted (APPEND l1 l2)) ==>
      (!l : 'elt list.
         prefix1 (0 : int) l = []) ==>
      (!n : int.
       !x : 'elt.
       !l : 'elt list.
         (0 : int) < n ==>
         prefix1 n (x::l) =
           x::prefix1 (n - (1 : int)) l) ==>
      !l : 'elt list.
        let n = &(LENGTH l)
        in
          (~(n < (2 : int)) ==>
           (2 : int) <= n /\ n <= &(LENGTH l)) /\
          (!result : 'elt list.
             (if n < (2 : int) then
                result = l
              else
                sorted result /\ PERM result (prefix1 n l)) ==>
             sorted result /\ PERM result l)``;
