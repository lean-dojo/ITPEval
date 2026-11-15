(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_altqtvc: the alternative
  doubly linked list to balanced binary-search-tree verification condition,
  preserving finite-map domains and frames, inorder locations, tree size,
  and the height balance bound. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory finite_mapTheory pred_setTheory;

Datatype:
  dllbst_tree =
    DllBstEmpty
  | DllBstNode dllbst_tree int dllbst_tree
End

val dllbst_to_num_def = Define `
  dllbst_to_num (z : int) = if z < 0 then 0 else Num z`;

val dllbst_at_def = Define `
  dllbst_at (s : 'loc list) (i : int) = EL (dllbst_to_num i) s`;

val dllbst_power_def = Define `
  dllbst_power (base : int) (exponent : int) =
    base ** dllbst_to_num exponent`;

val dllbst_valid_def = Define `
  dllbst_valid null prev next (s : 'loc list) <=>
    !i : int.
      0 <= i /\ i < &(LENGTH s) ==>
      dllbst_at s i <> null /\
      dllbst_at s i IN FDOM prev /\
      dllbst_at s i IN FDOM next /\
      (!j : int.
         i < j /\ j < &(LENGTH s) ==>
         dllbst_at s i <> dllbst_at s j)`;

val dllbst_dll_def = Define `
  dllbst_dll null prev next (s : 'loc list) head lo hi <=>
    dllbst_valid null prev next s /\
    0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
    head = (if lo = &(LENGTH s) then null else dllbst_at s lo) /\
    (!i : int.
       lo <= i /\ i < hi - 1 ==>
       next ' (dllbst_at s i) = dllbst_at s (i + 1)) /\
    (!i : int.
       lo < i /\ i < hi ==>
       prev ' (dllbst_at s i) = dllbst_at s (i - 1)) /\
    (lo < hi ==>
       next ' (dllbst_at s (hi - 1)) =
         (if hi = &(LENGTH s) then null else dllbst_at s hi)) /\
    (lo < hi ==>
       prev ' (dllbst_at s lo) =
         (if lo = 0 then null else dllbst_at s (lo - 1)))`;

val dllbst_tree_def = Define `
  (dllbst_tree null prev next (s : 'loc list) root DllBstEmpty lo hi <=>
     dllbst_valid null prev next s /\
     0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
     root = null /\ lo = hi) /\
  (dllbst_tree null prev next s root (DllBstNode l p r) lo hi <=>
     dllbst_valid null prev next s /\
     0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
     lo <= p /\ p < hi /\
     root = dllbst_at s p /\
     dllbst_tree null prev next s (prev ' root) l lo p /\
     dllbst_tree null prev next s (next ' root) r (p + 1) hi)`;

val dllbst_size_def = Define `
  (dllbst_size DllBstEmpty = (0 : int)) /\
  (dllbst_size (DllBstNode l p r) =
     (1 : int) + dllbst_size l + dllbst_size r)`;

val dllbst_height_def = Define `
  (dllbst_height DllBstEmpty = (0 : int)) /\
  (dllbst_height (DllBstNode l p r) =
     (1 : int) +
       (if dllbst_height l <= dllbst_height r
        then dllbst_height r
        else dllbst_height l))`;

val dllbst_inorder_def = Define `
  (dllbst_inorder (s : 'loc list) DllBstEmpty = []) /\
  (dllbst_inorder s (DllBstNode l p r) =
     dllbst_inorder s l ++
     dllbst_at s p :: dllbst_inorder s r)`;

val verifythis_2021_dll_to_bst_Top_dll_to_bst_alt_vc =
  ``!(to_fmap : 'state -> 'loc |-> 'loc)
      (null : 'loc)
      (prev : 'state)
      (next : 'state)
      (s : 'loc list)
      (head : 'loc).
      dllbst_dll null (to_fmap prev) (to_fmap next)
        s head 0 (&(LENGTH s)) ==>
      (dllbst_dll null (to_fmap prev) (to_fmap next)
         s head 0 (&(LENGTH s)) /\
       let n = &(LENGTH s) in
         dllbst_dll null (to_fmap prev) (to_fmap next)
           s head 0 (0 + n) /\
         !next1 prev1 o1 o2.
           (dllbst_tree null (to_fmap prev1) (to_fmap next1)
              s o1 o2 0 (0 + n) /\
            FDOM (to_fmap prev1) = FDOM (to_fmap prev) /\
            FDOM (to_fmap next1) = FDOM (to_fmap next) /\
            (!i : int.
               0 <= i /\ i < 0 ==>
               to_fmap prev1 ' (dllbst_at s i) =
                 to_fmap prev ' (dllbst_at s i)) /\
            (!i : int.
               0 + n <= i /\ i < &(LENGTH s) ==>
               to_fmap prev1 ' (dllbst_at s i) =
                 to_fmap prev ' (dllbst_at s i)) /\
            (!i : int.
               0 <= i /\ i < 0 ==>
               to_fmap next1 ' (dllbst_at s i) =
                 to_fmap next ' (dllbst_at s i)) /\
            (!i : int.
               0 + n <= i /\ i < &(LENGTH s) ==>
               to_fmap next1 ' (dllbst_at s i) =
                 to_fmap next ' (dllbst_at s i)) /\
            (0 < n ==>
               let h = dllbst_height o2 in
                 dllbst_power 2 (h - 1) <= n /\
                 n < dllbst_power 2 h)) ==>
           (dllbst_tree null (to_fmap prev1) (to_fmap next1)
              s o1 o2 0 (&(LENGTH s)) /\
            dllbst_size o2 = &(LENGTH s) /\
            dllbst_inorder s o2 = s /\
            (0 < &(LENGTH s) ==>
               let h = dllbst_height o2 in
                 dllbst_power 2 (h - 1) <= &(LENGTH s) /\
                 &(LENGTH s) < dllbst_power 2 h)))``;
