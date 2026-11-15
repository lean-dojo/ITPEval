(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_recqtvc: the recursive
  conversion of a doubly linked list segment into a height-balanced binary
  search tree while preserving finite-map domains and untouched links outside
  each recursive segment. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
val _ = load "finite_mapTheory";
open integerTheory listTheory finite_mapTheory pred_setTheory;

Datatype:
  dllbst_rec_tree =
    DllBstRecEmpty
  | DllBstRecNode dllbst_rec_tree int dllbst_rec_tree
End

val dllbst_rec_to_num_def = Define `
  dllbst_rec_to_num (z : int) = if z < 0 then 0 else Num z`;

val dllbst_rec_at_def = Define `
  dllbst_rec_at (s : 'loc list) (i : int) =
    EL (dllbst_rec_to_num i) s`;

val dllbst_rec_boundary_def = Define `
  dllbst_rec_boundary null (s : 'loc list) (i : int) =
    if i = &(LENGTH s) then null else dllbst_rec_at s i`;

val dllbst_rec_power_def = Define `
  dllbst_rec_power (base : int) (exponent : int) =
    base ** dllbst_rec_to_num exponent`;

val dllbst_rec_valid_def = Define `
  dllbst_rec_valid null prev next (s : 'loc list) <=>
    !i : int.
      0 <= i /\ i < &(LENGTH s) ==>
      dllbst_rec_at s i <> null /\
      dllbst_rec_at s i IN FDOM prev /\
      dllbst_rec_at s i IN FDOM next /\
      (!j : int.
         i < j /\ j < &(LENGTH s) ==>
         dllbst_rec_at s i <> dllbst_rec_at s j)`;

val dllbst_rec_dll_def = Define `
  dllbst_rec_dll null prev next (s : 'loc list) head lo hi <=>
    dllbst_rec_valid null prev next s /\
    0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
    head = dllbst_rec_boundary null s lo /\
    (!i : int.
       lo <= i /\ i < hi - 1 ==>
       next ' (dllbst_rec_at s i) = dllbst_rec_at s (i + 1)) /\
    (!i : int.
       lo < i /\ i < hi ==>
       prev ' (dllbst_rec_at s i) = dllbst_rec_at s (i - 1)) /\
    (lo < hi ==>
       next ' (dllbst_rec_at s (hi - 1)) =
         dllbst_rec_boundary null s hi) /\
    (lo < hi ==>
       prev ' (dllbst_rec_at s lo) =
         (if lo = 0 then null else dllbst_rec_at s (lo - 1)))`;

val dllbst_rec_tree_def = Define `
  (dllbst_rec_tree_rel null prev next (s : 'loc list) root
      DllBstRecEmpty lo hi <=>
     dllbst_rec_valid null prev next s /\
     0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
     root = null /\ lo = hi) /\
  (dllbst_rec_tree_rel null prev next s root
      (DllBstRecNode l p r) lo hi <=>
     dllbst_rec_valid null prev next s /\
     0 <= lo /\ lo <= hi /\ hi <= &(LENGTH s) /\
     lo <= p /\ p < hi /\
     root = dllbst_rec_at s p /\
     dllbst_rec_tree_rel null prev next s
       (prev ' root) l lo p /\
     dllbst_rec_tree_rel null prev next s
       (next ' root) r (p + 1) hi)`;

val dllbst_rec_height_def = Define `
  (dllbst_rec_height DllBstRecEmpty = (0 : int)) /\
  (dllbst_rec_height (DllBstRecNode l p r) =
     (1 : int) +
       (if dllbst_rec_height l <= dllbst_rec_height r
        then dllbst_rec_height r
        else dllbst_rec_height l))`;

val dllbst_rec_balance_def = Define `
  dllbst_rec_balance t (n : int) <=>
    0 < n ==>
    let h = dllbst_rec_height t in
      dllbst_rec_power 2 (h - 1) <= n /\
      n < dllbst_rec_power 2 h`;

val dllbst_rec_frame_def = Define `
  dllbst_rec_frame new old (s : 'loc list) lo hi <=>
    (!i : int.
       0 <= i /\ i < lo ==>
       new ' (dllbst_rec_at s i) =
         old ' (dllbst_rec_at s i)) /\
    (!i : int.
       hi <= i /\ i < &(LENGTH s) ==>
       new ' (dllbst_rec_at s i) =
         old ' (dllbst_rec_at s i))`;

val dllbst_rec_the_def = Define `
  dllbst_rec_the (opt : 'a option) =
    case opt of
      NONE => ARB
    | SOME x => x`;

val verifythis_2021_dll_to_bst_Top_dll_to_bst_rec_vc =
  ``!(to_fmap : 'state -> 'loc |-> 'loc)
      (null : 'loc)
      (prev : 'state)
      (next : 'state)
      (s : 'loc list)
      (head : 'loc)
      (ihead : int)
      (n : int).
      dllbst_rec_dll null (to_fmap prev) (to_fmap next)
        s head ihead (ihead + n) ==>
      if n = 0 then
        head = dllbst_rec_boundary null s (ihead + n) /\
        dllbst_rec_tree_rel null (to_fmap prev) (to_fmap next)
          s null DllBstRecEmpty ihead (ihead + n) /\
        FDOM (to_fmap prev) = FDOM (to_fmap prev) /\
        FDOM (to_fmap next) = FDOM (to_fmap next) /\
        dllbst_rec_balance DllBstRecEmpty n
      else
        ~((2 : int) = 0) /\
        let nl = n quot (2 : int) in
          (((0 : int) <= n /\ nl < n) /\
           dllbst_rec_dll null (to_fmap prev) (to_fmap next)
             s head ihead (ihead + nl)) /\
          !next1 prev1 left1 l.
            dllbst_rec_tree_rel null
                (to_fmap prev1) (to_fmap next1)
                s left1 l ihead (ihead + nl) /\
            FDOM (to_fmap prev1) = FDOM (to_fmap prev) /\
            FDOM (to_fmap next1) = FDOM (to_fmap next) /\
            dllbst_rec_frame
              (to_fmap prev1) (to_fmap prev)
              s ihead (ihead + nl) /\
            dllbst_rec_frame
              (to_fmap next1) (to_fmap next)
              s ihead (ihead + nl) /\
            dllbst_rec_balance l nl ==>
            dllbst_rec_boundary null s (ihead + nl) IN
              FDOM (to_fmap prev1) /\
            !prev2.
              to_fmap prev2 =
                to_fmap prev1 |+
                  (dllbst_rec_boundary null s (ihead + nl), left1) ==>
              let o1 = n - nl - (1 : int) in
              let o2 = ihead + nl + (1 : int) in
              let root =
                dllbst_rec_boundary null s (ihead + nl)
              in
                root IN FDOM (to_fmap next1) /\
                let o3 = to_fmap next1 ' root in
                  o3 =
                      dllbst_rec_the
                        (FLOOKUP (to_fmap next1) root) ==>
                  (((0 : int) <= n /\ o1 < n) /\
                   dllbst_rec_dll null
                     (to_fmap prev2) (to_fmap next1)
                     s o3 o2 (o2 + o1)) /\
                  !next2 prev3 temp r.
                    dllbst_rec_tree_rel null
                        (to_fmap prev3) (to_fmap next2)
                        s temp r o2 (o2 + o1) /\
                    FDOM (to_fmap prev3) =
                      FDOM (to_fmap prev2) /\
                    FDOM (to_fmap next2) =
                      FDOM (to_fmap next1) /\
                    dllbst_rec_frame
                      (to_fmap prev3) (to_fmap prev2)
                      s o2 (o2 + o1) /\
                    dllbst_rec_frame
                      (to_fmap next2) (to_fmap next1)
                      s o2 (o2 + o1) /\
                    dllbst_rec_balance r o1 ==>
                    root IN FDOM (to_fmap next2) /\
                    !next3.
                      to_fmap next3 =
                        to_fmap next2 |+ (root, temp) ==>
                      let o4 =
                        DllBstRecNode l (ihead + nl) r
                      in
                        dllbst_rec_boundary null s (o2 + o1) =
                          dllbst_rec_boundary null s (ihead + n) /\
                        dllbst_rec_tree_rel null
                          (to_fmap prev3) (to_fmap next3)
                          s root o4 ihead (ihead + n) /\
                        FDOM (to_fmap prev3) =
                          FDOM (to_fmap prev) /\
                        FDOM (to_fmap next3) =
                          FDOM (to_fmap next) /\
                        dllbst_rec_frame
                          (to_fmap prev3) (to_fmap prev)
                          s ihead (ihead + n) /\
                        dllbst_rec_frame
                          (to_fmap next3) (to_fmap next)
                          s ihead (ihead + n) /\
                        dllbst_rec_balance o4 n``;
