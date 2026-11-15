(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_not_exists_c_post_2_part1_goal21:
  a memccpy verification condition equating two reads after a havoced byte
  memory is updated at one address, under integer bounds, writable-region,
  separation, address-order, linking, constancy, and non-occurrence
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal21 =
  ``let mc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mc_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let mc_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int.
       \n : int.
       \q : int # int.
        if mc_separated q 1 p n then m1 q else m0 q
    in
    let mc_update =
      \f : (int # int) -> int.
       \p : int # int.
       \v : int.
       \q : int # int.
        if q = p then v else f q
    in
    let mc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mc_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let mc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let mc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_sint8 : int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int. mc_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          mc_is_sint8 z ==>
          to_sint8 z = z) ==>
        !a_1 : int # int.
        !i_1 i : int.
        !t_1 t_2 : (int # int) -> int.
        !a : int # int.
        !i_3 i_2 : int.
        !t : int -> int.
          let a_2 = mc_shift a_1 0 in
          let x = i_1 - i in
          let a_3 = mc_havoc t_1 t_2 a_2 x in
          let a_4 = mc_shift a x in
          let a_5 = a_3 a_4 in
          let a_6 = mc_shift a 0 in
          let a_7 = mc_shift a_1 x in
          let a_8 = mc_update a_3 a_7 a_5 in
            i <> 0 ==>
            a_5 = to_sint8 i_3 ==>
            0 < i_1 ==>
            0 <= i ==>
            i <= i_1 ==>
            0 <= i_2 ==>
            i_2 < i_1 ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            -128 <= i_3 ==>
            i_3 <= 127 ==>
            linked t ==>
            sconst t_2 ==>
            mc_is_uint32 i ==>
            mc_is_uint32 i_1 ==>
            mc_is_sint32 i_3 ==>
            mc_valid_rw t a_6 i_1 ==>
            mc_valid_rw t a_2 i_1 ==>
            mc_separated a_6 i_1 a_2 i_1 ==>
            addr_le a a_4 ==>
            addr_le a_1 a_7 ==>
            addr_le a_4 (mc_shift a i_1) ==>
            addr_le a_7 (mc_shift a_1 i_1) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 + i < i_1 ==>
              a_3 (mc_shift a_1 i_4) =
              a_3 (mc_shift a i_4)) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 < i_1 ==>
              a_5 <> t_2 (mc_shift a i_4)) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 + i < i_1 ==>
              a_5 <> a_3 (mc_shift a_1 i_4)) ==>
            a_8 (mc_shift a_1 i_2) =
            a_8 (mc_shift a i_2)``;
