(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_rev_sortqtvc: the reverse-order
  mergesort verification condition, covering its base cases, recursive
  prefix split, sorted merge preconditions, and permutation postcondition.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val mergesort_list_OCamlMergesort_rev_sort_vc =
  ``!(le : 'elt -> 'elt -> bool)
      (sorted : 'elt list -> bool)
      (prefix1 : int -> 'elt list -> 'elt list).
      (!x : 'elt. le x x) ==>
      (!x y z : 'elt. le x y /\ le y z ==> le x z) ==>
      (!x y : 'elt. le x y \/ le y x) ==>
      sorted [] ==>
      (!x : 'elt. sorted [x]) ==>
      (!x y : 'elt.
       !xs : 'elt list.
         le x y ==>
         sorted (y::xs) ==>
         sorted (x::y::xs)) ==>
      (!xs : 'elt list.
       !x : 'elt.
         ((!y : 'elt. MEM y xs ==> le x y) /\ sorted xs) <=>
         sorted (x::xs)) ==>
      (!xs ys : 'elt list.
         (sorted xs /\
          sorted ys /\
          (!x y : 'elt.
             MEM x xs ==>
             MEM y ys ==>
             le x y)) <=>
         sorted (APPEND xs ys)) ==>
      (!xs : 'elt list.
         prefix1 (0 : int) xs = []) ==>
      (!m : int.
       !x : 'elt.
       !xs : 'elt list.
         (0 : int) < m ==>
         prefix1 m (x::xs) =
           x::prefix1 (m - (1 : int)) xs) ==>
      !n : int.
      !l : 'elt list.
        (2 : int) <= n ==>
        n <= &(LENGTH l) ==>
        ((if n = (2 : int) then
            case l of
              x1::x2::rest => T
            | _ => F
          else if n = (3 : int) then
            case l of
              x1::x2::x3::rest => T
            | _ => F
          else
            ~((2 : int) = (0 : int)) /\
            let n1 = n quot (2 : int)
            in
              let n2 = n - n1
              in
                ((0 : int) <= n1 /\
                 n1 <= &(LENGTH l)) /\
                (!l2 : 'elt list.
                   l = APPEND (prefix1 n1 l) l2 ==>
                   (((0 : int) <= n /\ n1 < n) /\
                    (2 : int) <= n1 /\
                    n1 <= &(LENGTH l)) /\
                   (!s1 : 'elt list.
                      sorted s1 /\
                      PERM s1 (prefix1 n1 l) ==>
                      (((0 : int) <= n /\ n2 < n) /\
                       (2 : int) <= n2 /\
                       n2 <= &(LENGTH l2)) /\
                      (!s2 : 'elt list.
                         sorted s2 /\
                         PERM s2 (prefix1 n2 l2) ==>
                         let o1 = ([] : 'elt list)
                         in
                           (sorted (REVERSE o1) /\
                            sorted s1 /\
                            sorted s2) /\
                           (!x y : 'elt.
                              MEM x o1 ==>
                              MEM y s1 ==>
                              le x y) /\
                           (!x y : 'elt.
                              MEM x o1 ==>
                              MEM y s2 ==>
                              le x y))))) /\
         (!result : 'elt list.
            (if n = (2 : int) then
               case l of
                 x1::x2::rest =>
                   if ~(le x1 x2) then
                     result = [x1; x2]
                   else
                     result = [x2; x1]
               | _ => F
             else if n = (3 : int) then
               case l of
                 x1::x2::x3::rest =>
                   if ~(le x1 x2) then
                     if ~(le x2 x3) then
                       result = [x1; x2; x3]
                     else if ~(le x1 x3) then
                       result = [x1; x3; x2]
                     else
                       result = [x3; x1; x2]
                   else if ~(le x1 x3) then
                     result = [x2; x1; x3]
                   else if ~(le x2 x3) then
                     result = [x2; x3; x1]
                   else
                     result = [x3; x2; x1]
               | _ => F
             else
               let n1 = n quot (2 : int)
               in
                 ?l2 : 'elt list.
                   l = APPEND (prefix1 n1 l) l2 /\
                   ?s1 : 'elt list.
                     (sorted s1 /\
                      PERM s1 (prefix1 n1 l)) /\
                     ?s2 : 'elt list.
                       (sorted s2 /\
                        PERM s2 (prefix1 (n - n1) l2)) /\
                       sorted (REVERSE result) /\
                       PERM result
                         (APPEND (APPEND ([] : 'elt list) s1) s2)) ==>
            sorted (REVERSE result) /\
            PERM result (prefix1 n l)))``;
