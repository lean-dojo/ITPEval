(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_stdio/__fflush_Why3_ide_VC__fflush_call_write_pre_goal31:
  under modeled stdio-file validity, address-order, framing, linking,
  integer-range, and writable-memory conditions, a nested-shift integer
  memory read is nonnegative. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal31 =
  ``let ff_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ff_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ff_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let ff_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ff_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ff_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ff_p_valid_file =
      \malloc : int -> int.
       \mint : (int # int) -> int.
       \f : int # int.
        0 <= mint (ff_shift f 0) /\
        ff_valid_rw malloc f 3
    in
    let ff_p_valid_io_file_pvt_norec =
      \addr_le : (int # int) -> (int # int) -> bool.
       \addr_lt : (int # int) -> (int # int) -> bool.
       \malloc : int -> int.
       \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \f : int # int.
        let x = mint (ff_shift f 9) in
        let x_1 = mint (ff_shift f 7) in
        let x_2 = mint (ff_shift f 8) in
        let a = mptr (ff_shift f 5) in
        let a_1 = mptr (ff_shift f 6) in
        let a_2 = mptr (ff_shift f 4) in
        let a_3 = mptr (ff_shift f 3) in
        let a_4 = ff_shift a 0 in
        let x_3 = 32 + x in
          x = 16384 /\
          0 <= x_1 /\
          x_1 < x /\
          0 <= x_2 /\
          x_2 < x /\
          ff_valid_rw malloc f 11 /\
          addr_le a a_1 /\
          ff_p_valid_file malloc mint (ff_shift f 0) /\
          ff_valid_rw malloc a_2 11 /\
          ff_valid_rw malloc a_3 11 /\
          ff_separated f 11 a_2 11 /\
          ff_separated f 11 a_3 11 /\
          ff_separated a_2 11 a_3 11 /\
          ff_valid_rw malloc a_4 x_3 /\
          ff_separated f 11 a_4 x_3 /\
          ff_separated a_2 11 a_4 x_3 /\
          ff_separated a_3 11 a_4 x_3 /\
          addr_lt a_1 (ff_shift a x_3)
    in
    let ff_p_valid_io_file_pvt =
      \addr_le : (int # int) -> (int # int) -> bool.
       \addr_lt : (int # int) -> (int # int) -> bool.
       \malloc : int -> int.
       \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \f : int # int.
        let x = mint (ff_shift f 9) in
        let a = mptr (ff_shift f 6) in
        let a_1 = mptr (ff_shift f 5) in
        let a_2 = mptr (ff_shift f 3) in
        let a_3 = mptr (ff_shift f 4) in
        let x_1 = mint (ff_shift f 7) in
        let x_2 = mint (ff_shift f 8) in
        let a_4 = ff_shift a_1 0 in
        let x_3 = 32 + x in
          x = 16384 /\
          FST a = FST a_1 /\
          mptr (ff_shift a_2 4) = f /\
          mptr (ff_shift a_3 3) = f /\
          0 <= x_1 /\
          x_1 < x /\
          0 <= x_2 /\
          x_2 < x /\
          ff_valid_rw malloc f 11 /\
          addr_le a_1 a /\
          ff_p_valid_file malloc mint (ff_shift f 0) /\
          ff_separated f 11 a_3 11 /\
          ff_separated f 11 a_2 11 /\
          ff_separated a_3 11 a_2 11 /\
          ff_p_valid_io_file_pvt_norec
            addr_le addr_lt malloc mptr mint a_3 /\
          ff_p_valid_io_file_pvt_norec
            addr_le addr_lt malloc mptr mint a_2 /\
          ff_valid_rw malloc a_4 x_3 /\
          ff_separated f 11 a_4 x_3 /\
          ff_separated a_3 11 a_4 x_3 /\
          ff_separated a_2 11 a_4 x_3 /\
          addr_lt a (ff_shift a_1 x_3)
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !t_2 : (int # int) -> (int # int).
      !a_1 a : int # int.
      !t_1 : (int # int) -> int.
      !i i_1 : int.
      !t : int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        let a_2 = t_2 (ff_shift a_1 5) in
        let x = FST a_2 in
        let x_1 = FST a in
        let x_2 = FST (t_2 (ff_shift a_1 6)) in
        let x_3 = t_1 (ff_shift a_1 9) in
        let x_4 = t_1 (ff_shift (ff_shift a_1 0) 0) in
          i <> 0 ==>
          t_1 (ff_shift a_1 7) = 0 ==>
          x = x_1 ==>
          x_2 = x_1 ==>
          x_2 = x ==>
          0 <= i ==>
          i_1 <= i ==>
          region (FST a_1) <= 0 ==>
          -1 <= i_1 ==>
          ff_framed region t_2 ==>
          linked t ==>
          ff_is_uint32 i ==>
          ff_is_sint32 i_1 ==>
          ff_is_uint32 x_3 ==>
          ff_is_uint32 (t_1 (ff_shift a_1 8)) ==>
          ff_p_valid_io_file_pvt
            addr_le addr_lt t t_2 t_1 a_1 ==>
          addr_le a_2 a ==>
          ff_valid_rw t (ff_shift a 0) i ==>
          ff_is_sint32 x_4 ==>
          addr_le a (ff_shift a_2 (32 + x_3)) ==>
          0 <= x_4``;
