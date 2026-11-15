(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strcasecmp_Why3_ide_VCstrcasecmp_not_eq_post_part2_goal19:
  a strcasecmp verification condition concluding that two strings differ
  before a corresponding address, under string-length, byte-case conversion,
  memory separation, address-order, and integer-range assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal19 =
  ``let mc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mc_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let mc_length_of_str_is =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \n : int.
        mchar (mc_shift s n) = 0 /\
        0 <= n /\
        mc_valid_rw malloc (mc_shift s 0) (1 + n) /\
        (!j : int.
          0 <= j ==>
          j < n ==>
          mchar (mc_shift s j) <> 0)
    in
    let mc_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let mc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let mc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let mc_is_lower =
      \z : int. 97 <= z /\ z <= 122
    in
    let mc_is_upper =
      \z : int. 65 <= z /\ z <= 90
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !l_length : ((int # int) -> int) -> (int # int) -> int.
      !to_uint8 : int -> int.
      !l_toupper : int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!malloc : int -> int.
         !mchar : (int # int) -> int.
         !s : int # int.
         !n : int.
          mc_length_of_str_is malloc mchar s n ==>
          l_length mchar s = n) ==>
        (!z : int. mc_is_uint8 (to_uint8 z)) ==>
        (!z : int.
          mc_is_uint8 z ==>
          to_uint8 z = z) ==>
        (!c : int.
          mc_is_uint8 c ==>
          mc_is_sint8 (l_toupper c)) ==>
        (!c : int.
          mc_is_uint8 c ==>
          mc_is_lower c ==>
          32 + l_toupper c = c /\
          (!j : int.
            mc_is_uint8 j ==>
            mc_is_upper j ==>
            l_toupper j = j /\
            (!k : int.
              mc_is_uint8 k ==>
              ~mc_is_lower k ==>
              ~mc_is_upper k ==>
              l_toupper k = k))) ==>
        !a a_1 a_2 : int # int.
        !t_1 : (int # int) -> int.
        !i_5 i_6 : int.
        !t : int -> int.
        !i i_1 i_4 i_2 i_3 : int.
          let x = FST a in
          let x_1 = SND a_1 in
          let x_2 = SND a in
          let a_3 = mc_shift a_2 (x_1 - x_2) in
          let x_3 = t_1 a_1 in
          let x_4 = l_length t_1 a in
          let x_5 = l_length t_1 a_2 in
          let x_6 = to_uint8 x_3 in
            FST a_1 = x ==>
            l_toupper (to_uint8 (t_1 (mc_shift a_2 i_5))) <>
              l_toupper (to_uint8 (t_1 (mc_shift a i_5))) ==>
            t_1 a_3 = 0 ==>
            0 <= i_5 ==>
            i_5 <= i_6 ==>
            0 <= x_3 ==>
            region x <= 0 ==>
            region (FST a_2) <= 0 ==>
            x_3 <= 255 ==>
            linked t ==>
            sconst t_1 ==>
            mc_is_sint32 i ==>
            addr_le a a_1 ==>
            mc_is_sint8 x_3 ==>
            mc_length_of_str_is t t_1 a i_1 ==>
            mc_length_of_str_is t t_1 a i_4 ==>
            mc_length_of_str_is t t_1 a i_6 ==>
            mc_length_of_str_is t t_1 a_2 i_2 ==>
            mc_length_of_str_is t t_1 a_2 i_3 ==>
            mc_length_of_str_is t t_1 a_2 i_6 ==>
            addr_le a_1 (mc_shift a x_4) ==>
            mc_separated
              (mc_shift a_2 0) (1 + x_5)
              (mc_shift a 0) (1 + x_4) ==>
            addr_le a_2 a_3 ==>
            addr_le a_3 (mc_shift a_2 x_5) ==>
            (mc_is_lower 0 ==> i = -32) ==>
            (mc_is_upper 0 ==> i = 0) ==>
            (~mc_is_lower 0 ==> ~mc_is_upper 0 ==> i = 0) ==>
            (mc_is_upper x_6 ==> x_3 = i) ==>
            (mc_is_lower x_6 ==> x_3 = 32 + i) ==>
            (~mc_is_lower x_6 ==> ~mc_is_upper x_6 ==> x_3 = i) ==>
            ~(!i_7 : int.
              0 <= i_7 ==>
              i_7 + x_2 < x_1 ==>
              l_toupper (to_uint8 (t_1 (mc_shift a_2 i_7))) =
              l_toupper (to_uint8 (t_1 (mc_shift a i_7))))``;
