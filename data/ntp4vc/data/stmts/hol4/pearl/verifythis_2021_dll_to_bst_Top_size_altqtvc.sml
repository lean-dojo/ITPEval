(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_size_altqtvc: preservation of the
  doubly linked list segment invariant and strict decrease of the remaining
  length during iterative list-size traversal. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
val _ = load "finite_mapTheory";
open integerTheory listTheory finite_mapTheory pred_setTheory;

val dllbst_size_alt_to_num_def = Define `
  dllbst_size_alt_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val dllbst_size_alt_at_def = Define `
  dllbst_size_alt_at (s : 'loc list) (i : int) =
    EL (dllbst_size_alt_to_num i) s`;

val dllbst_size_alt_the_def = Define `
  dllbst_size_alt_the (opt : 'a option) =
    case opt of
      NONE => ARB
    | SOME x => x`;

val dllbst_size_alt_valid_def = Define `
  dllbst_size_alt_valid null prev next (s : 'loc list) <=>
    !i : int.
      0 <= i /\ i < &(LENGTH s) ==>
      dllbst_size_alt_at s i <> null /\
      dllbst_size_alt_at s i IN FDOM prev /\
      dllbst_size_alt_at s i IN FDOM next /\
      (!j : int.
         i < j /\ j < &(LENGTH s) ==>
         dllbst_size_alt_at s i <> dllbst_size_alt_at s j)`;

val dllbst_size_alt_dll_def = Define `
  dllbst_size_alt_dll null prev next (s : 'loc list) head lo hi <=>
    dllbst_size_alt_valid null prev next s /\
    0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
    head =
      (if lo = &(LENGTH s)
       then null
       else dllbst_size_alt_at s lo) /\
    (!i : int.
       lo <= i /\ i < hi - 1 ==>
       next ' (dllbst_size_alt_at s i) =
         dllbst_size_alt_at s (i + 1)) /\
    (!i : int.
       lo < i /\ i < hi ==>
       prev ' (dllbst_size_alt_at s i) =
         dllbst_size_alt_at s (i - 1)) /\
    (lo < hi ==>
       next ' (dllbst_size_alt_at s (hi - 1)) =
         (if hi = &(LENGTH s)
          then null
          else dllbst_size_alt_at s hi)) /\
    (lo < hi ==>
       prev ' (dllbst_size_alt_at s lo) =
         (if lo = 0
          then null
          else dllbst_size_alt_at s (lo - 1)))`;

val verifythis_2021_dll_to_bst_Top_size_alt_vc =
  ``!(to_fmap : 'state -> 'loc |-> 'loc)
      (null : 'loc)
      (prev : 'state)
      (next : 'state)
      (s : 'loc list)
      (head : 'loc).
      dllbst_size_alt_dll null (to_fmap prev) (to_fmap next)
        s head 0 (&(LENGTH s)) ==>
      (dllbst_size_alt_dll null (to_fmap prev) (to_fmap next)
         s head 0 (&(LENGTH s)) /\
       !len : int. !p : 'loc.
         dllbst_size_alt_dll null (to_fmap prev) (to_fmap next)
           s p len (&(LENGTH s)) ==>
         if p <> null then
           p IN FDOM (to_fmap next) /\
           (let o1 = to_fmap next ' p in
              o1 =
                  dllbst_size_alt_the
                    (FLOOKUP (to_fmap next) p) ==>
              ((0 <= &(LENGTH s) - len /\
                &(LENGTH s) - (len + 1) <
                  &(LENGTH s) - len) /\
               dllbst_size_alt_dll null
                 (to_fmap prev) (to_fmap next)
                 s o1 (len + 1) (&(LENGTH s))))
         else
           len = &(LENGTH s))``;
