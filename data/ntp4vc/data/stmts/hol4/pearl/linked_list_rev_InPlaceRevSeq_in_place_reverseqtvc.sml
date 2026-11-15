(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_InPlaceRevSeq_in_place_reverseqtvc: a verification
  condition for the loop invariant of in-place reversal of a null-terminated
  linked-list segment, including one next-pointer update step. This file
  contains no proof.
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

val linked_list_rev_InPlaceRevSeq_in_place_reverse_vc =
  ``!(null : 'loc)
      (eq_loc : 'loc -> 'loc -> bool)
      (next1 : 'loc -> 'loc)
      (l : 'loc)
      (lM : 'loc list).
      (!x y. (eq_loc x y <=> x = y)) ==>
      ll_list_seg null next1 l lM null ==>
      ll_list_seg null next1 l lM null /\
      ll_list_seg null next1 null [] null /\
      ll_disjoint lM [] /\
      APPEND (REVERSE lM) [] = REVERSE lM /\
      !rM : 'loc list.
      !r : 'loc.
      !pM : 'loc list.
      !p : 'loc.
      !next2 : 'loc -> 'loc.
        ll_list_seg null next2 p pM null /\
        ll_list_seg null next2 r rM null /\
        ll_disjoint pM rM /\
        APPEND (REVERSE pM) rM = REVERSE lM ==>
        let o1 = null
        in
        let o2 = eq_loc p o1
        in
          (o2 <=> p = o1) ==>
          if ~o2 then
            ~(p = null) /\
            ~(p = null) /\
            (let o3 = EL 0 pM
             in
             let o4 = o3::rM
             in
               (&(LENGTH o4) =
                  (1 : int) + &(LENGTH rM) /\
                EL 0 o4 = o3 /\
                (!i : int.
                   (0 : int) < i /\
                   i <= &(LENGTH rM) ==>
                   EL (Num i) o4 =
                     EL (Num (i - (1 : int))) rM)) ==>
               (((0 : int) <= (1 : int) /\
                 (1 : int) <= &(LENGTH pM)) /\
                ((0 : int) <= &(LENGTH pM) /\
                 LENGTH (DROP 1 pM) < LENGTH pM) /\
                ll_list_seg null
                  (ll_fun_update next2 p r)
                  (next2 p) (DROP 1 pM) null /\
                ll_list_seg null
                  (ll_fun_update next2 p r)
                  p o4 null /\
                ll_disjoint (DROP 1 pM) o4 /\
                APPEND (REVERSE (DROP 1 pM)) o4 =
                  REVERSE lM))
          else
            ll_list_seg null next2 r (REVERSE lM) null``;
