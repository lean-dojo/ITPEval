(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_loop_inv_2_established_part2_goal4:
  a memccpy loop-invariant establishment condition asserting address order
  after a positive integer shift, under integer-range, memory-validity,
  separation, linking, and constancy assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal4 =
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
    let mc_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let mc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        !a a_1 : int # int.
        !i i_1 : int.
        !t : int -> int.
        !t_1 : (int # int) -> int.
          let a_2 = mc_shift a 0 in
          let a_3 = mc_shift a_1 0 in
            0 < i ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            -128 <= i_1 ==>
            i_1 <= 127 ==>
            linked t ==>
            sconst t_1 ==>
            mc_is_uint32 i ==>
            mc_is_sint32 i_1 ==>
            mc_valid_rw t a_2 i ==>
            mc_valid_rw t a_3 i ==>
            mc_separated a_2 i a_3 i ==>
            addr_le a_1 (mc_shift a_1 i)``;
