(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/list_removal_Top_remove2qtvc: a linked-list removal verification
  condition over an abstract pointer heap, including the traversal invariant
  and the pointer update that removes the distinguished entry. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val list_removal_remove2_fun_update_def = Define `
  list_removal_remove2_fun_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \x. if x = k then v else f x`;

val list_removal_Top_remove2_vc =
  ``!(null : 'loc)
      (head : 'loc)
      (entry : 'loc)
      (listp : ('loc -> 'loc) -> 'loc -> int -> 'loc -> bool)
      (n1 : int)
      (n2 : int)
      (mem1 : 'loc -> 'loc).
      ~(head = null) /\
      ~(entry = null) /\
      ~(head = entry) /\
      (!n : int.
       !mem2 : 'loc -> 'loc.
       !x : 'loc.
       !y : 'loc.
         (0 : int) <= n ==>
         if n = (0 : int) then
           (listp mem2 x n y <=> x = y)
         else
           (listp mem2 x n y <=>
              ~(x = null) /\
              listp mem2 (mem2 x) (n - (1 : int)) y)) /\
      (0 : int) < n1 /\
      (0 : int) < n2 /\
      listp mem1 head n1 entry /\
      listp mem1 entry n2 null ==>
      (0 : int) < (1 : int) /\
      (1 : int) <= n1 /\
      ~(head = null) /\
      listp mem1 head ((1 : int) - (1 : int)) head /\
      listp mem1 (mem1 head) (n1 - (1 : int)) entry /\
      listp mem1 entry n2 null /\
      !n : int.
      !ind : 'loc.
        (((0 : int) < n /\ n <= n1) /\
         ~(ind = null) /\
         listp mem1 head (n - (1 : int)) ind /\
         listp mem1 (mem1 ind) (n1 - n) entry /\
         listp mem1 entry n2 null) ==>
        ~(ind = null) /\
        if ~(mem1 ind = entry) then
          ~(ind = null) /\
          ((0 : int) <= n1 - n /\
           n1 - (n + (1 : int)) < n1 - n) /\
          ((0 : int) < n + (1 : int) /\
           n + (1 : int) <= n1) /\
          ~(mem1 ind = null) /\
          listp mem1 head
            (n + (1 : int) - (1 : int)) (mem1 ind) /\
          listp mem1 (mem1 (mem1 ind))
            (n1 - (n + (1 : int))) entry /\
          listp mem1 entry n2 null
        else
          let o1 = entry
          in
            ~(o1 = null) /\
            ~(ind = null) /\
            listp
              (list_removal_remove2_fun_update mem1 ind (mem1 o1))
              head (n1 + n2 - (1 : int)) null``;
