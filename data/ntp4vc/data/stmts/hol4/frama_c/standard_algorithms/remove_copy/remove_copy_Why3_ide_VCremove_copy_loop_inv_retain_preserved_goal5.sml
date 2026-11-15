(*
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/remove_copy/remove_copy_Why3_ide_VCremove_copy_loop_inv_retain_preserved_goal5:
  preservation of the remove-copy loop's multiset-retention invariant across
  one conditional memory update. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val remove_copy_shift_def = new_definition (
  "remove_copy_shift_def",
  ``remove_copy_shift (p : int # int) (k : int) =
      (FST p, SND p + k)``);

val remove_copy_separated_def = new_definition (
  "remove_copy_separated_def",
  ``remove_copy_separated
      (p : int # int) (n : int) (q : int # int) (m : int) <=>
      n <= 0 \/
      m <= 0 \/
      FST p <> FST q \/
      SND q + m <= SND p \/
      SND p + n <= SND q``);

val remove_copy_valid_rw_def = new_definition (
  "remove_copy_valid_rw_def",
  ``remove_copy_valid_rw
      (memory_size : int -> int) (p : int # int) (n : int) <=>
      0 < n ==>
      0 < FST p /\
      0 <= SND p /\
      SND p + n <= memory_size (FST p)``);

val remove_copy_valid_rd_def = new_definition (
  "remove_copy_valid_rd_def",
  ``remove_copy_valid_rd
      (memory_size : int -> int) (p : int # int) (n : int) <=>
      0 < n ==>
      FST p <> 0 /\
      0 <= SND p /\
      SND p + n <= memory_size (FST p)``);

val remove_copy_is_uint32_def = new_definition (
  "remove_copy_is_uint32_def",
  ``remove_copy_is_uint32 (x : int) <=> 0 <= x /\ x < 4294967296``);

val remove_copy_is_sint32_def = new_definition (
  "remove_copy_is_sint32_def",
  ``remove_copy_is_sint32 (x : int) <=>
      -2147483648 <= x /\ x < 2147483648``);

val remove_copy_havoc_def = new_definition (
  "remove_copy_havoc_def",
  ``remove_copy_havoc
      (before : (int # int) -> int)
      (after : (int # int) -> int)
      (p : int # int) (n : int) (q : int # int) =
      if remove_copy_separated q 1 p n then after q else before q``);

val remove_copy_unchanged_def = new_definition (
  "remove_copy_unchanged_def",
  ``remove_copy_unchanged
      (before : (int # int) -> int)
      (after : (int # int) -> int)
      (a : int # int) (m : int) (n : int) <=>
      !j : int.
        m <= j ==>
        j < n ==>
        after (remove_copy_shift a j) = before (remove_copy_shift a j)``);

val remove_copy_has_value_def = new_definition (
  "remove_copy_has_value_def",
  ``remove_copy_has_value
      (memory : (int # int) -> int)
      (a : int # int) (m : int) (n : int) (v : int) <=>
      ?j : int.
        memory (remove_copy_shift a j) = v /\
        m <= j /\
        j < n``);

val remove_copy_retain_rest_def = new_definition (
  "remove_copy_retain_rest_def",
  ``remove_copy_retain_rest
      (count :
        ((int # int) -> int) -> (int # int) ->
        int -> int -> int -> int)
      (source : (int # int) -> int)
      (destination : (int # int) -> int)
      (source_base : int # int) (source_lo : int) (source_hi : int)
      (destination_base : int # int)
      (destination_lo : int) (destination_hi : int)
      (removed : int) <=>
      !value : int.
        value <> removed ==>
        remove_copy_is_sint32 value ==>
        count destination source_base source_lo source_hi value =
        count source destination_base destination_lo destination_hi value``);

val remove_copy_count_axioms_def = new_definition (
  "remove_copy_count_axioms_def",
  ``remove_copy_count_axioms
      (count :
        ((int # int) -> int) -> (int # int) ->
        int -> int -> int -> int) <=>
      (!n m v (memory : (int # int) -> int) (a : int # int).
        n <= m /\
        remove_copy_is_sint32 v ==>
        count memory a m n v = 0) /\
      (!n (memory : (int # int) -> int) (a : int # int) v m.
        memory (remove_copy_shift a (n - 1)) = v ==>
        m < n ==>
        remove_copy_is_sint32 v ==>
        1 + count memory a m (n - 1) v = count memory a m n v) /\
      (!n (memory : (int # int) -> int) (a : int # int) v m.
        memory (remove_copy_shift a (n - 1)) <> v ==>
        m < n ==>
        remove_copy_is_sint32 v ==>
        count memory a m (n - 1) v = count memory a m n v) /\
      (!v
        (before : (int # int) -> int)
        (after : (int # int) -> int)
        (a : int # int) m n.
        remove_copy_is_sint32 v /\
        remove_copy_unchanged before after a m n ==>
        count after a m n v = count before a m n v)``);

val remove_copy_Why3_ide_VCremove_copy_loop_inv_retain_preserved_goal5 =
  ``!(count :
        ((int # int) -> int) -> (int # int) ->
        int -> int -> int -> int)
      (region : int -> int)
      (linked : (int -> int) -> bool)
      (t_3 : (int # int) -> int)
      (a_1 : int # int)
      (i_5 : int)
      (i : int)
      (a : int # int)
      (t_1 : (int # int) -> int)
      (i_2 : int)
      (t : int -> int)
      (i_1 : int)
      (i_3 : int)
      (i_4 : int)
      (t_2 : (int # int) -> int)
      (p : bool).
      remove_copy_count_axioms count ==>
      let x = count t_3 a_1 0 i_5 i in
      let x_1 = 1 + i_5 in
      let a_2 = remove_copy_shift a_1 0 in
      let a_3 = remove_copy_shift a_1 i_5 in
      let a_4 = remove_copy_shift a 0 in
      let x_2 = i_5 - x in
      let a_5 = remove_copy_havoc t_1 t_3 a_4 i_2 in
      let a_6 = a_5 a_3 in
      let a_7 = remove_copy_shift a x_2 in
        i_5 <= i_2 ==>
        i_5 < i_2 ==>
        region (FST a) <= 0 ==>
        region (FST a_1) <= 0 ==>
        x <= i_5 ==>
        0 <= x ==>
        i_5 <= 4294967294 ==>
        linked t ==>
        remove_copy_is_uint32 i_1 ==>
        remove_copy_is_uint32 i_2 ==>
        remove_copy_is_uint32 i_3 ==>
        remove_copy_is_uint32 i_4 ==>
        remove_copy_is_uint32 i_5 ==>
        remove_copy_is_sint32 i ==>
        remove_copy_is_uint32 x_1 ==>
        remove_copy_valid_rd t a_2 i_2 ==>
        remove_copy_valid_rd t a_3 1 ==>
        remove_copy_valid_rw t a_4 i_2 ==>
        remove_copy_separated a_2 i_2 a 1 ==>
        remove_copy_is_uint32 x_2 ==>
        remove_copy_is_sint32 a_6 ==>
        ~remove_copy_has_value a_5 a 0 x_2 i ==>
        remove_copy_unchanged a_5 t_3 a_1 i_5 i_2 ==>
        remove_copy_unchanged a_5 t_3 a x_2 i_2 ==>
        remove_copy_retain_rest
          count a_5 t_3 a_1 0 i_5 a 0 x_2 i ==>
        (if a_6 = i then
           a_5 = t_2 /\
           i_4 + count t_3 a_1 0 i_5 (t_2 a_3) = i_5
         else
           p = F /\
           i_3 = i_1 /\
           i_1 + x = i_5 /\
           i_3 + x = i_5 /\
           i_4 + x = x_1 /\
           (\q. if q = a_7 then a_6 else a_5 q) = t_2 /\
           i_5 <= 4294967294 + x /\
           remove_copy_valid_rw t a_7 1) ==>
        remove_copy_retain_rest
          count t_2 t_3 a_1 0 x_1 a 0 i_4 i``;
