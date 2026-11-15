(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_chopqtvc: the list-chopping
  verification condition, establishing recursive-call bounds and
  reconstruction from an abstract prefix operation. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val mergesort_list_OCamlMergesort_chop_vc =
  ``!(prefix1 : int -> 'a list -> 'a list).
      (!xs : 'a list.
         prefix1 (0 : int) xs = []) /\
      (!m : int.
       !x : 'a.
       !xs : 'a list.
         (0 : int) < m ==>
         prefix1 m (x::xs) =
           x::prefix1 (m - (1 : int)) xs) ==>
      !n : int.
      !l : 'a list.
        (0 : int) <= n ==>
        n <= &(LENGTH l) ==>
        ((~(n = (0 : int)) ==>
          case l of
            [] => F
          | h::t =>
              let o1 = n - (1 : int)
              in
                ((0 : int) <= n /\ o1 < n) /\
                (0 : int) <= o1 /\
                o1 <= &(LENGTH t)) /\
         (!result : 'a list.
            (if n = (0 : int) then
               result = l
             else
               case l of
                 [] => F
               | h::t =>
                   t =
                     APPEND
                       (prefix1 (n - (1 : int)) t)
                       result) ==>
            l = APPEND (prefix1 n l) result))``;
