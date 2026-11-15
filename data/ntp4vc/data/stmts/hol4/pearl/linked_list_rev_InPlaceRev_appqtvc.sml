(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRev_appqtvc: a verification condition for
  appending two disjoint null-terminated linked-list segments by traversing
  the first segment and updating its final link. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val ll_disjoint_def = Define `
  ll_disjoint (s1 : 'a list) (s2 : 'a list) <=>
    !i1 : int.
      (0 : int) <= i1 /\ i1 < &(LENGTH s1) ==>
      !i2 : int.
        (0 : int) <= i2 /\ i2 < &(LENGTH s2) ==>
        ~(EL (Num i1) s1 = EL (Num i2) s2)`;

val ll_list_seg_def = Define `
  ll_list_seg
    (null : 'loc)
    (next1 : 'loc -> 'loc)
    (p : 'loc)
    (s : 'loc list)
    (q : 'loc) <=>
      let n = &(LENGTH s)
      in
        (!i : int.
           (0 : int) <= i /\ i < n ==>
           ~(EL (Num i) s = null)) /\
        ((p = q /\ n = (0 : int)) \/
         ((1 : int) <= n /\
          EL 0 s = p /\
          next1 (EL (Num (n - (1 : int))) s) = q /\
          !i : int.
            (0 : int) <= i /\ i < n - (1 : int) ==>
            next1 (EL (Num i) s) =
              EL (Num (i + (1 : int))) s))`;

val ll_fun_update_def = Define `
  ll_fun_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \x. if x = k then v else f x`;

val linked_list_rev_InPlaceRev_app_vc =
  ``!(null : 'loc)
      (eq_loc : 'loc -> 'loc -> bool)
      (next1 : 'loc -> 'loc)
      (l1 : 'loc)
      (l1M : 'loc list)
      (l2 : 'loc)
      (l2M : 'loc list).
      (!x y. (eq_loc x y <=> x = y)) ==>
      ll_list_seg null next1 l1 l1M null ==>
      ll_list_seg null next1 l2 l2M null ==>
      ll_disjoint l1M l2M ==>
      let o1 = null
      in
      let o2 = eq_loc l1 o1
      in
        (o2 <=> l1 = o1) ==>
        if o2 then
          ll_list_seg null next1 l2 (APPEND l1M l2M) null
        else
          (~(l1 = null) /\
           ll_list_seg null next1 l1 [] l1 /\
           ll_list_seg null next1 l1 l1M null /\
           APPEND [] l1M = l1M /\
           ll_disjoint [] l1M) /\
          !l1pM pM p.
            ~(p = null) /\
            ll_list_seg null next1 l1 l1pM p /\
            ll_list_seg null next1 p pM null /\
            APPEND l1pM pM = l1M /\
            ll_disjoint l1pM pM ==>
            let o3 = null
            in
              ~(p = null) /\
              let o4 = next1 p
              in
              let o5 = eq_loc o4 o3
              in
                (o5 <=> o4 = o3) ==>
                if ~o5 then
                  case pM of
                    [] => F
                  | h::t =>
                      ~(p = null) /\
                      (case pM of
                         [] => F
                       | h'::f => f = t) /\
                      ~(next1 p = null) /\
                      ll_list_seg null next1
                        l1 (APPEND l1pM [h]) (next1 p) /\
                      ll_list_seg null next1
                        (next1 p) t null /\
                      APPEND (APPEND l1pM [h]) t = l1M /\
                      ll_disjoint (APPEND l1pM [h]) t
                else
                  ~(p = null) /\
                  ll_list_seg null
                    (ll_fun_update next1 p l2)
                    l1 (APPEND l1M l2M) null``;
