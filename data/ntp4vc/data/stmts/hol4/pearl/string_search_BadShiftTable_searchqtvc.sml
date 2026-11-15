(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/string_search_BadShiftTable_searchqtvc: the verification condition
  for bad-character-shift string search, including its search invariant,
  shift-table lookup, termination decrease, and result specification. This
  file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory integer_wordTheory listTheory optionTheory wordsTheory;

val search_to_num_def = Define `
  search_to_num (z : int) = if z < 0 then 0 else Num z`;

val search_substring_def = Define `
  search_substring
      (text : (8 word) list)
      (start : int)
      (len : int) =
    TAKE (search_to_num len) (DROP (search_to_num start) text)`;

val search_char_at_def = Define `
  search_char_at (text : (8 word) list) (i : int) =
    if search_to_num i < LENGTH text then
      EL (search_to_num i) text
    else
      ARB`;

val search_mem_def = Define `
  search_mem (m : (8 word) -> (63 word) option) (c : 8 word) <=>
    ~(m c = NONE)`;

val search_lookup_def = Define `
  search_lookup (m : (8 word) -> (63 word) option) (c : 8 word) =
    case m c of
      NONE => ARB
    | SOME value => value`;

val search_int63_in_bounds_def = Define `
  search_int63_in_bounds (z : int) <=>
    (-4611686018427387904 : int) <= z /\
    z <= (4611686018427387903 : int)`;

val search_matches_def = Define `
  search_matches
      (pat : (8 word) list)
      (text : (8 word) list)
      (p : int) <=>
    (0 : int) <= p /\
    p <= &(LENGTH text) - &(LENGTH pat) /\
    search_substring text p (&(LENGTH pat)) = pat`;

val search_record_inv_def = Define `
  search_record_inv
      (to_fmap : 'state -> (8 word) -> (63 word) option)
      (pat : (8 word) list)
      (sht : 'state) <=>
    (!j : int.
       !c : 8 word.
         (0 : int) <= j /\ j < &(LENGTH pat) ==>
         c = search_char_at pat j ==>
         search_mem (to_fmap sht) c) /\
    (!c : 8 word.
       search_mem (to_fmap sht) c ==>
       (1 : int) <= w2i (search_lookup (to_fmap sht) c) /\
       w2i (search_lookup (to_fmap sht) c) <=
         &(LENGTH pat) + (1 : int)) /\
    (!c : 8 word.
       search_mem (to_fmap sht) c ==>
       !j : int.
         (1 : int) <= j /\
         j < w2i (search_lookup (to_fmap sht) c) ==>
         ~(search_char_at pat (&(LENGTH pat) - j) = c))`;

val string_search_BadShiftTable_search_vc =
  ``!(to_fmap : 'state -> (8 word) -> (63 word) option).
    !(pat : 'bad_shift_table -> (8 word) list).
    !(sht : 'bad_shift_table -> 'state).
      (!self : 'bad_shift_table.
         search_record_inv to_fmap (pat self) (sht self)) ==>
      (!a b : 'bad_shift_table.
         pat a = pat b /\ sht a = sht b ==> a = b) ==>
      !bst : 'bad_shift_table.
      !text : (8 word) list.
        &(LENGTH (pat bst)) <= &(LENGTH text) ==>
        let pat1 = pat bst
        in
          !m : 63 word.
            w2i m = &(LENGTH pat1) /\
            (0 : int) <= &(LENGTH pat1) ==>
            !n : 63 word.
              w2i n = &(LENGTH text) /\
              (0 : int) <= &(LENGTH text) ==>
              (((0 : int) <= (0 : int) /\
                (0 : int) <= w2i n) /\
               (!j : int.
                  (0 : int) <= j /\ j < (0 : int) ==>
                  j <= w2i n - w2i m ==>
                  ~(search_substring text j (w2i m) = pat1))) /\
              (!i : 63 word.
                 (((0 : int) <= w2i i /\ w2i i <= w2i n) /\
                  (!j : int.
                     (0 : int) <= j /\ j < w2i i ==>
                     j <= w2i n - w2i m ==>
                     ~(search_substring text j (w2i m) = pat1))) ==>
                 search_int63_in_bounds (w2i n - w2i m) /\
                 !o1 : 63 word.
                   w2i o1 = w2i n - w2i m ==>
                   if w2i i <= w2i o1 then
                     ((0 : int) <= w2i i /\
                      w2i i <=
                        &(LENGTH text) - &(LENGTH pat1)) /\
                     (if search_matches pat1 text (w2i i) then
                        ((~(1 : int)) <= w2i i /\
                         w2i i <=
                           &(LENGTH text) -
                           &(LENGTH (pat bst))) /\
                        (if w2i i = ~(1 : int) then
                           !j : int.
                             ~(search_matches (pat bst) text j)
                         else
                           search_matches (pat bst) text (w2i i))
                      else
                        search_int63_in_bounds (w2i n - w2i m) /\
                        !o2 : 63 word.
                          w2i o2 = w2i n - w2i m ==>
                          (w2i i = w2i o2 ==> i = o2) ==>
                          if i = o2 then
                            ((~(1 : int)) <= ~(1 : int) /\
                             (~(1 : int)) <=
                               &(LENGTH text) -
                               &(LENGTH (pat bst))) /\
                            (!j : int.
                               ~(search_matches (pat bst) text j))
                          else
                            search_int63_in_bounds (w2i i + w2i m) /\
                            !o3 : 63 word.
                              w2i o3 = w2i i + w2i m ==>
                              ((0 : int) <= w2i o3 /\
                               w2i o3 < &(LENGTH text)) /\
                              (let c = search_char_at text (w2i o3)
                               in
                                 (if search_mem
                                       (to_fmap (sht bst)) c
                                  then
                                    search_mem
                                      (to_fmap (sht bst)) c
                                  else
                                    search_int63_in_bounds
                                      (w2i m + (1 : int))) /\
                                 !o4 : 63 word.
                                   (if search_mem
                                         (to_fmap (sht bst)) c
                                    then
                                      let shift_table = sht bst
                                      in
                                        o4 =
                                          search_lookup
                                            (to_fmap shift_table) c /\
                                        o4 =
                                          search_lookup
                                            (to_fmap shift_table) c
                                    else
                                      w2i o4 =
                                        w2i m + (1 : int)) ==>
                                   search_int63_in_bounds
                                     (w2i i + w2i o4) /\
                                   !o5 : 63 word.
                                     w2i o5 = w2i i + w2i o4 ==>
                                     ((0 : int) <=
                                        w2i n - w2i m - w2i i /\
                                      w2i n - w2i m - w2i o5 <
                                        w2i n - w2i m - w2i i) /\
                                     ((0 : int) <= w2i o5 /\
                                      w2i o5 <= w2i n) /\
                                     (!j : int.
                                        (0 : int) <= j /\
                                        j < w2i o5 ==>
                                        j <= w2i n - w2i m ==>
                                        ~(search_substring
                                            text j (w2i m) =
                                          pat1))))
                   else
                     ((~(1 : int)) <= ~(1 : int) /\
                      (~(1 : int)) <=
                        &(LENGTH text) -
                        &(LENGTH (pat bst))) /\
                     (!j : int.
                        ~(search_matches (pat bst) text j)))``;
