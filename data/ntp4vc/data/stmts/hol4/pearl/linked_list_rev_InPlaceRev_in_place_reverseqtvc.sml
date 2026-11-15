(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRev_in_place_reverseqtvc: a verification
  condition for the loop invariant of in-place reversal of a null-terminated
  linked-list segment, including one next-pointer update step. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open listTheory;

val ll_disjoint_def = Define `
  ll_disjoint (l1 : 'a list) (l2 : 'a list) <=>
    !x. ~(MEM x l1 /\ MEM x l2)`;

val ll_list_seg_def = Define `
  (ll_list_seg
     (null : 'loc)
     (p : 'loc)
     (next : 'loc -> 'loc)
     ([] : 'loc list)
     (q : 'loc) <=>
       p = q) /\
  (ll_list_seg null p next (h::t) q <=>
     h = p /\
     ~(p = null) /\
     ll_list_seg null (next p) next t q)`;

val ll_fun_update_def = Define `
  ll_fun_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \x. if x = k then v else f x`;

val linked_list_rev_InPlaceRev_in_place_reverse_vc =
  ``!(null : 'loc)
      (eq_loc : 'loc -> 'loc -> bool)
      (l : 'loc)
      (next : 'loc -> 'loc)
      (lM : 'loc list).
      (!l1 l2. (eq_loc l1 l2 <=> l1 = l2)) ==>
      ll_list_seg null l next lM null ==>
      ll_list_seg null l next lM null /\
      ll_list_seg null null next [] null /\
      ll_disjoint lM [] /\
      APPEND (REVERSE lM) [] = REVERSE lM /\
      !rM : 'loc list.
      !r : 'loc.
      !pM : 'loc list.
      !p : 'loc.
      !next1 : 'loc -> 'loc.
        ll_list_seg null p next1 pM null /\
        ll_list_seg null r next1 rM null /\
        ll_disjoint pM rM /\
        APPEND (REVERSE pM) rM = REVERSE lM ==>
        let o1 = null
        in
        let o2 = eq_loc p o1
        in
          (o2 <=> p = o1) ==>
          if ~o2 then
            ~(p = null) /\
            (case pM of
               [] => F
             | h::t =>
                 (case pM of
                    [] => F
                  | h0::f => f = t) /\
                 ll_list_seg null
                   (next1 p)
                   (ll_fun_update next1 p r)
                   t
                   null /\
                 ll_list_seg null
                   p
                   (ll_fun_update next1 p r)
                   (h::rM)
                   null /\
                 ll_disjoint t (h::rM) /\
                 APPEND (REVERSE t) (h::rM) = REVERSE lM)
          else
            ll_list_seg null r next1 (REVERSE lM) null``;
