(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_dll_to_bstqtvc: the top-level doubly
  linked list to balanced binary-search-tree verification condition,
  preserving finite-map domains and frames, inorder locations, tree size,
  and the height balance bound. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
val _ = load "finite_mapTheory";
open integerTheory listTheory finite_mapTheory pred_setTheory;

Datatype:
  dllbst_main_tree =
    DllBstMainEmpty
  | DllBstMainNode dllbst_main_tree int dllbst_main_tree
End

val dllbst_main_to_num_def = Define `
  dllbst_main_to_num (z : int) = if z < 0 then 0 else Num z`;

val dllbst_main_at_def = Define `
  dllbst_main_at (s : 'loc list) (i : int) =
    EL (dllbst_main_to_num i) s`;

val dllbst_main_power_def = Define `
  dllbst_main_power (base : int) (exponent : int) =
    base ** dllbst_main_to_num exponent`;

val dllbst_main_valid_def = Define `
  dllbst_main_valid null prev next (s : 'loc list) <=>
    !i : int.
      0 <= i /\ i < &(LENGTH s) ==>
      dllbst_main_at s i <> null /\
      dllbst_main_at s i IN FDOM prev /\
      dllbst_main_at s i IN FDOM next /\
      (!j : int.
         i < j /\ j < &(LENGTH s) ==>
         dllbst_main_at s i <> dllbst_main_at s j)`;

val dllbst_main_dll_def = Define `
  dllbst_main_dll null prev next (s : 'loc list) head lo hi <=>
    dllbst_main_valid null prev next s /\
    0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
    head =
      (if lo = &(LENGTH s) then null else dllbst_main_at s lo) /\
    (!i : int.
       lo <= i /\ i < hi - 1 ==>
       next ' (dllbst_main_at s i) = dllbst_main_at s (i + 1)) /\
    (!i : int.
       lo < i /\ i < hi ==>
       prev ' (dllbst_main_at s i) = dllbst_main_at s (i - 1)) /\
    (lo < hi ==>
       next ' (dllbst_main_at s (hi - 1)) =
         (if hi = &(LENGTH s) then null else dllbst_main_at s hi)) /\
    (lo < hi ==>
       prev ' (dllbst_main_at s lo) =
         (if lo = 0 then null else dllbst_main_at s (lo - 1)))`;

val dllbst_main_tree_def = Define `
  (dllbst_main_tree_rel null prev next (s : 'loc list) root
      DllBstMainEmpty lo hi <=>
     dllbst_main_valid null prev next s /\
     0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
     root = null /\ lo = hi) /\
  (dllbst_main_tree_rel null prev next s root
      (DllBstMainNode l p r) lo hi <=>
     dllbst_main_valid null prev next s /\
     0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
     lo <= p /\ p < hi /\
     root = dllbst_main_at s p /\
     dllbst_main_tree_rel null prev next s
       (prev ' root) l lo p /\
     dllbst_main_tree_rel null prev next s
       (next ' root) r (p + 1) hi)`;

val dllbst_main_size_def = Define `
  (dllbst_main_size DllBstMainEmpty = (0 : int)) /\
  (dllbst_main_size (DllBstMainNode l p r) =
     (1 : int) + dllbst_main_size l + dllbst_main_size r)`;

val dllbst_main_height_def = Define `
  (dllbst_main_height DllBstMainEmpty = (0 : int)) /\
  (dllbst_main_height (DllBstMainNode l p r) =
     (1 : int) +
       (if dllbst_main_height l <= dllbst_main_height r
        then dllbst_main_height r
        else dllbst_main_height l))`;

val dllbst_main_inorder_def = Define `
  (dllbst_main_inorder (s : 'loc list) DllBstMainEmpty = []) /\
  (dllbst_main_inorder s (DllBstMainNode l p r) =
     dllbst_main_inorder s l ++
     dllbst_main_at s p :: dllbst_main_inorder s r)`;

val verifythis_2021_dll_to_bst_Top_dll_to_bst_vc =
  ``!(to_fmap : 'state -> 'loc |-> 'loc)
      (null : 'loc)
      (prev : 'state)
      (next : 'state)
      (s : 'loc list)
      (head : 'loc).
      dllbst_main_dll null (to_fmap prev) (to_fmap next)
        s head 0 (&(LENGTH s)) ==>
      (dllbst_main_dll null (to_fmap prev) (to_fmap next)
         s head 0 (&(LENGTH s)) /\
       let n = &(LENGTH s) - (0 : int) in
         dllbst_main_dll null (to_fmap prev) (to_fmap next)
           s head 0 (0 + n) /\
         !next1 prev1 o1 o2.
           (dllbst_main_tree_rel null
              (to_fmap prev1) (to_fmap next1)
              s o1 o2 0 (0 + n) /\
            FDOM (to_fmap prev1) = FDOM (to_fmap prev) /\
            FDOM (to_fmap next1) = FDOM (to_fmap next) /\
            (!i : int.
               0 <= i /\ i < 0 ==>
               to_fmap prev1 ' (dllbst_main_at s i) =
                 to_fmap prev ' (dllbst_main_at s i)) /\
            (!i : int.
               0 + n <= i /\ i < &(LENGTH s) ==>
               to_fmap prev1 ' (dllbst_main_at s i) =
                 to_fmap prev ' (dllbst_main_at s i)) /\
            (!i : int.
               0 <= i /\ i < 0 ==>
               to_fmap next1 ' (dllbst_main_at s i) =
                 to_fmap next ' (dllbst_main_at s i)) /\
            (!i : int.
               0 + n <= i /\ i < &(LENGTH s) ==>
               to_fmap next1 ' (dllbst_main_at s i) =
                 to_fmap next ' (dllbst_main_at s i)) /\
            (0 < n ==>
               let h = dllbst_main_height o2 in
                 dllbst_main_power 2 (h - 1) <= n /\
                 n < dllbst_main_power 2 h)) ==>
           (dllbst_main_tree_rel null
              (to_fmap prev1) (to_fmap next1)
              s o1 o2 0 (&(LENGTH s)) /\
            dllbst_main_size o2 = &(LENGTH s) /\
            dllbst_main_inorder s o2 = s /\
            (0 < &(LENGTH s) ==>
               let h = dllbst_main_height o2 in
                 dllbst_main_power 2 (h - 1) <= &(LENGTH s) /\
                 &(LENGTH s) < dllbst_main_power 2 h)))``;
