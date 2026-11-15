(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/list_removal_Top_remove1qtvc: a linked-list removal verification
  condition over an abstract pointer heap, including the loop invariant and
  the pointer update that removes the distinguished entry. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val list_removal_fun_update_def = Define `
  list_removal_fun_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \x. if x = k then v else f x`;

val list_removal_Top_remove1_vc =
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
      let o1 = head
      in
        ~(o1 = null) /\
        let o2 = mem1 o1
        in
          (((0 : int) < (1 : int) /\ (1 : int) <= n1) /\
           listp mem1 head (1 : int) o2 /\
           ~(o2 = null) /\
           listp mem1 o2 (n1 - (1 : int)) entry /\
           listp mem1 entry n2 null) /\
          !n : int.
          !curr : 'loc.
          !prev : 'loc.
            ((0 : int) < n /\ n <= n1) /\
            listp mem1 head n curr /\
            ~(curr = null) /\
            (prev = null ==> n = (1 : int)) /\
            (~(prev = null) ==> mem1 prev = curr) /\
            (~(prev = null) ==>
               listp mem1 head (n - (1 : int)) prev) /\
            listp mem1 curr (n1 - n) entry /\
            listp mem1 entry n2 null ==>
            if ~(curr = entry) then
              ~(curr = null) /\
              ((0 : int) <= n1 - n /\
               n1 - (n + (1 : int)) < n1 - n) /\
              ((0 : int) < n + (1 : int) /\
               n + (1 : int) <= n1) /\
              listp mem1 head (n + (1 : int)) (mem1 curr) /\
              ~(mem1 curr = null) /\
              (curr = null ==> n + (1 : int) = (1 : int)) /\
              (~(curr = null) ==> T) /\
              (~(curr = null) ==>
                 listp mem1 head
                   (n + (1 : int) - (1 : int)) curr) /\
              listp mem1 (mem1 curr)
                (n1 - (n + (1 : int))) entry /\
              listp mem1 entry n2 null
            else if prev = null then
              ~(curr = null) /\
              let o3 = head
              in
                ~(o3 = null) /\
                listp
                  (list_removal_fun_update mem1 o3 (mem1 curr))
                  head (n1 + n2 - (1 : int)) null
            else
              ~(curr = null) /\
              ~(prev = null) /\
              listp
                (list_removal_fun_update mem1 prev (mem1 curr))
                head (n1 + n2 - (1 : int)) null``;
