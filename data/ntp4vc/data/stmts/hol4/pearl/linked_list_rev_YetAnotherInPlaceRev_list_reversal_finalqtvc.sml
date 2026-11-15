(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_YetAnotherInPlaceRev_list_reversal_finalqtvc: the
  final verification condition for reversing a null-terminated linked list,
  relating forward and reverse sequence layouts while preserving heap cells
  outside the list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

val llrev_valid_cells_def = Define `
  llrev_valid_cells
    (null : 'loc)
    (s : int -> 'loc)
    (n : int) <=>
      (!i : int.
         (0 : int) <= i /\ i < n ==>
         ~(s i = null)) /\
      (!i j : int.
         (0 : int) <= i /\ i < n ==>
         (0 : int) <= j /\ j < n ==>
         ~(i = j) ==>
         ~(s i = s j))`;

val llrev_listLR_def = Define `
  llrev_listLR
    (null : 'loc)
    (next : 'loc -> 'loc)
    (s : int -> 'loc)
    (l : 'loc)
    (lo : int)
    (hi : int) <=>
      ((0 : int) <= lo /\ lo <= hi) /\
      if lo = hi then
        l = null
      else
        l = s lo /\
        next (s (hi - (1 : int))) = null /\
        !k : int.
          lo <= k /\ k < hi - (1 : int) ==>
          next (s k) = s (k + (1 : int))`;

val llrev_listRL_def = Define `
  llrev_listRL
    (null : 'loc)
    (next : 'loc -> 'loc)
    (s : int -> 'loc)
    (l : 'loc)
    (lo : int)
    (hi : int) <=>
      ((0 : int) <= lo /\ lo <= hi) /\
      if lo = hi then
        l = null
      else
        next (s lo) = null /\
        l = s (hi - (1 : int)) /\
        !k : int.
          lo < k /\ k < hi ==>
          next (s k) = s (k - (1 : int))`;

val llrev_frame_def = Define `
  llrev_frame
    (next1 : 'loc -> 'loc)
    (next2 : 'loc -> 'loc)
    (s : int -> 'loc)
    (n : int) <=>
      !p : 'loc.
        (!i : int.
           (0 : int) <= i /\ i < n ==>
           ~(p = s i)) ==>
        next1 p = next2 p`;

val linked_list_rev_YetAnotherInPlaceRev_list_reversal_final_vc =
  ``!(null : 'loc)
      (is_list :
        ('loc -> 'loc) -> 'loc -> (int -> 'loc) -> int -> bool)
      (result : (int -> 'loc) -> int -> 'loc)
      (fc : (int -> 'loc) -> int -> int -> 'loc)
      (mem1 : 'loc -> 'loc).
      (!s i.
         result s i = s (i + (1 : int))) /\
      (!n next l s.
         (0 : int) <= n ==>
         if n = (0 : int) then
           (is_list next l s n <=> l = null)
         else
           (is_list next l s n <=>
              (let q1 = s (0 : int)
               in
                 l = q1 /\ ~(q1 = null)) /\
              is_list
                next
                (next l)
                (result s)
                (n - (1 : int)))) /\
      (!s n i.
         fc s n i = s (n - (1 : int) - i)) ==>
      let mem2 = mem1
      in
        !s n l.
          (0 : int) <= n /\
          is_list mem2 l s n ==>
          (llrev_valid_cells null s n /\
           llrev_listLR null mem2 s l (0 : int) n) /\
          !mem3 : 'loc -> 'loc.
            let mem4 = mem3
            in
              !r : 'loc.
                llrev_listRL null mem4 s r (0 : int) n /\
                llrev_frame mem4 mem2 s n ==>
                is_list mem4 r (fc s n) n /\
                llrev_frame mem4 mem2 s n``;
