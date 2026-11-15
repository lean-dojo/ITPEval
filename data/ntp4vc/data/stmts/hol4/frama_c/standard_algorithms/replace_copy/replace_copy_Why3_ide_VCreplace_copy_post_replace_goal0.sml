(*
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/replace_copy/replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0:
  preservation of the replace-copy postcondition when the modeled destination
  memory update is restricted from length i_2 to length i_3. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0 =
  ``let rc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let rc_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/
        m <= 0 \/
        FST p <> FST q \/
        SND q + m <= SND p \/
        SND p + n <= SND q
    in
    let rc_havoc =
      \before : (int # int) -> int.
       \after : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if rc_separated q 1 p n then after q else before q
    in
    let rc_valid_rd =
      \allocation : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\
        0 <= SND p /\
        SND p + n <= allocation (FST p)
    in
    let rc_valid_rw =
      \allocation : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= allocation (FST p)
    in
    let rc_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let rc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let rc_unchanged =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \a : int # int. \lower : int. \upper : int.
        !j : int.
          lower <= j ==>
          j < upper ==>
          memory1 (rc_shift a j) = memory0 (rc_shift a j)
    in
    let rc_replace =
      \destination : (int # int) -> int.
       \source : (int # int) -> int.
       \source_base : int # int. \n : int.
       \destination_base : int # int.
       \old_value : int. \new_value : int.
        !j : int.
          let x = source (rc_shift source_base j) in
          let y = destination (rc_shift destination_base j) in
            0 <= j ==>
            j < n ==>
            (x = old_value ==> y = new_value) /\
            (x <> old_value ==> y = x)
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_1 a : int # int.
      !t_1 t_2 : (int # int) -> int.
      !i_2 i_3 : int.
      !t : int -> int.
      !i i_1 : int.
        let a_2 = rc_shift a_1 0 in
        let a_3 = rc_shift a 0 in
        let a_4 = rc_havoc t_1 t_2 a_3 i_2 in
          i_3 <= i_2 ==>
          0 <= i_3 ==>
          i_2 <= i_3 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          linked t ==>
          rc_is_uint32 i_2 ==>
          rc_is_uint32 i_3 ==>
          rc_is_sint32 i ==>
          rc_is_sint32 i_1 ==>
          rc_valid_rd t a_2 i_2 ==>
          rc_valid_rw t a_3 i_2 ==>
          rc_separated a_2 i_2 a 1 ==>
          rc_unchanged a_4 t_2 a_1 i_3 i_2 ==>
          rc_replace a_4 t_2 a_1 i_3 a i_1 i ==>
          rc_replace
            (rc_havoc t_1 t_2 a_3 i_3)
            t_2 a_1 i_3 a i_1 i``;
