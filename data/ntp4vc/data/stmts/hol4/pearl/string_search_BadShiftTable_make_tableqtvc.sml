(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/string_search_BadShiftTable_make_tableqtvc: the verification
  condition for constructing a bad-character shift table while preserving
  its prefix, shift-bound, and exclusion invariants. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory integer_wordTheory listTheory optionTheory wordsTheory;

val bst_to_num_def = Define `
  bst_to_num (z : int) = if z < 0 then 0 else Num z`;

val bst_char_at_def = Define `
  bst_char_at (pat : (8 word) list) (i : int) =
    if bst_to_num i < LENGTH pat then
      EL (bst_to_num i) pat
    else
      ARB`;

val bst_mem_def = Define `
  bst_mem (m : (8 word) -> (63 word) option) (c : 8 word) <=>
    ~(m c = NONE)`;

val bst_lookup_def = Define `
  bst_lookup (m : (8 word) -> (63 word) option) (c : 8 word) =
    case m c of
      NONE => ARB
    | SOME value => value`;

val bst_map_update_def = Define `
  bst_map_update
      (m : (8 word) -> (63 word) option)
      (key : 8 word)
      (value : 63 word) =
    \c. if c = key then SOME value else m c`;

val bst_int63_in_bounds_def = Define `
  bst_int63_in_bounds (z : int) <=>
    (-4611686018427387904 : int) <= z /\
    z <= (4611686018427387903 : int)`;

val bst_loop_inv_def = Define `
  bst_loop_inv
      (pat : (8 word) list)
      (m : (8 word) -> (63 word) option)
      (pat_length : int)
      (upper : int) <=>
    (!j : int.
       (0 : int) <= j /\ j < upper ==>
       bst_mem m (bst_char_at pat j)) /\
    (!c : 8 word.
       bst_mem m c ==>
       (1 : int) <= w2i (bst_lookup m c) /\
       w2i (bst_lookup m c) <= pat_length + (1 : int)) /\
    (!c : 8 word.
       bst_mem m c ==>
       !j : int.
         pat_length - w2i (bst_lookup m c) < j /\ j < upper ==>
         ~(bst_char_at pat j = c))`;

val bst_final_inv_def = Define `
  bst_final_inv
      (pat : (8 word) list)
      (m : (8 word) -> (63 word) option) <=>
    (!j : int.
       (0 : int) <= j /\ j < &(LENGTH pat) ==>
       bst_mem m (bst_char_at pat j)) /\
    (!c : 8 word.
       bst_mem m c ==>
       (1 : int) <= w2i (bst_lookup m c) /\
       w2i (bst_lookup m c) <= &(LENGTH pat) + (1 : int)) /\
    (!c : 8 word.
       bst_mem m c ==>
       !j : int.
         (1 : int) <= j /\ j < w2i (bst_lookup m c) ==>
         ~(bst_char_at pat (&(LENGTH pat) - j) = c))`;

val bst_record_inv_def = Define `
  bst_record_inv
      (to_fmap : 'state -> (8 word) -> (63 word) option)
      (pat : (8 word) list)
      (sht : 'state) <=>
    (!j : int.
       !c : 8 word.
         (0 : int) <= j /\ j < &(LENGTH pat) ==>
         c = bst_char_at pat j ==>
         bst_mem (to_fmap sht) c) /\
    (!c : 8 word.
       bst_mem (to_fmap sht) c ==>
       (1 : int) <= w2i (bst_lookup (to_fmap sht) c) /\
       w2i (bst_lookup (to_fmap sht) c) <=
         &(LENGTH pat) + (1 : int)) /\
    (!c : 8 word.
       bst_mem (to_fmap sht) c ==>
       !j : int.
         (1 : int) <= j /\
         j < w2i (bst_lookup (to_fmap sht) c) ==>
         ~(bst_char_at pat (&(LENGTH pat) - j) = c))`;

val string_search_BadShiftTable_make_table_vc =
  ``!(to_fmap : 'state -> (8 word) -> (63 word) option).
    !(pat : 'bad_shift_table -> (8 word) list).
    !(sht : 'bad_shift_table -> 'state).
      (!self : 'bad_shift_table.
         bst_record_inv to_fmap (pat self) (sht self)) ==>
      (!a b : 'bad_shift_table.
         pat a = pat b /\ sht a = sht b ==> a = b) ==>
      !m : 63 word.
      !pat1 : (8 word) list.
      !sht1 : 'state.
        w2i m = &(LENGTH pat1) ==>
        (0 : int) <= &(LENGTH pat1) ==>
        to_fmap sht1 = (\c : 8 word. NONE) ==>
        bst_int63_in_bounds (w2i m - (1 : int)) /\
        !o1 : 63 word.
          w2i o1 = w2i m - (1 : int) ==>
          (((0 : int) <= w2i o1 + (1 : int) ==>
             bst_loop_inv pat1 (to_fmap sht1) (w2i m) (0 : int) /\
             !sht2 : 'state.
               ((!i : 63 word.
                   let i1 = w2i i
                   in
                     (((0 : int) <= i1 /\ i1 <= w2i o1) /\
                      bst_loop_inv pat1 (to_fmap sht2) (w2i m) i1) ==>
                     bst_int63_in_bounds (w2i m - w2i i) /\
                     !o2 : 63 word.
                       w2i o2 = w2i m - w2i i ==>
                       ((0 : int) <= w2i i /\
                        w2i i < &(LENGTH pat1)) /\
                       !sht3 : 'state.
                         to_fmap sht3 =
                           bst_map_update
                             (to_fmap sht2)
                             (bst_char_at pat1 (w2i i))
                             o2 ==>
                         bst_loop_inv
                           pat1 (to_fmap sht3) (w2i m)
                           (i1 + (1 : int))) /\
                (bst_loop_inv
                   pat1 (to_fmap sht2) (w2i m)
                   (w2i o1 + (1 : int)) ==>
                 bst_final_inv pat1 (to_fmap sht2)))) /\
           (w2i o1 + (1 : int) < (0 : int) ==>
            bst_final_inv pat1 (to_fmap sht1)))``;
