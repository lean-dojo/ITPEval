(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_stdio/_fwrite_Why3_ide_VC_fwrite_call___fflush_pre_part4_goal16:
  under modeled framing, linking, integer-range, writable-memory, and
  stdio-file validity conditions, three integer-memory updates preserve the
  private I/O-file validity predicate. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal16 =
  ``let fw_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let fw_update =
      \f : (int # int) -> int. \k : int # int. \v : int.
       \p : int # int.
        if p = k then v else f p
    in
    let fw_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let fw_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let fw_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let fw_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let fw_p_valid_file =
      \malloc : int -> int.
       \mint : (int # int) -> int.
       \f : int # int.
        0 <= mint (fw_shift f 0) /\
        fw_valid_rw malloc f 3
    in
    let fw_p_valid_io_file_pvt_norec =
      \addr_le : (int # int) -> (int # int) -> bool.
       \addr_lt : (int # int) -> (int # int) -> bool.
       \malloc : int -> int.
       \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \f : int # int.
        let x = mint (fw_shift f 9) in
        let x_1 = mint (fw_shift f 7) in
        let x_2 = mint (fw_shift f 8) in
        let a = mptr (fw_shift f 5) in
        let a_1 = mptr (fw_shift f 6) in
        let a_2 = mptr (fw_shift f 4) in
        let a_3 = mptr (fw_shift f 3) in
        let a_4 = fw_shift a 0 in
        let x_3 = 32 + x in
          x = 16384 /\
          0 <= x_1 /\
          x_1 < x /\
          0 <= x_2 /\
          x_2 < x /\
          fw_valid_rw malloc f 11 /\
          addr_le a a_1 /\
          fw_p_valid_file malloc mint (fw_shift f 0) /\
          fw_valid_rw malloc a_2 11 /\
          fw_valid_rw malloc a_3 11 /\
          fw_separated f 11 a_2 11 /\
          fw_separated f 11 a_3 11 /\
          fw_separated a_2 11 a_3 11 /\
          fw_valid_rw malloc a_4 x_3 /\
          fw_separated f 11 a_4 x_3 /\
          fw_separated a_2 11 a_4 x_3 /\
          fw_separated a_3 11 a_4 x_3 /\
          addr_lt a_1 (fw_shift a x_3)
    in
    let fw_p_valid_io_file_pvt =
      \addr_le : (int # int) -> (int # int) -> bool.
       \addr_lt : (int # int) -> (int # int) -> bool.
       \malloc : int -> int.
       \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \f : int # int.
        let x = mint (fw_shift f 9) in
        let a = mptr (fw_shift f 6) in
        let a_1 = mptr (fw_shift f 5) in
        let a_2 = mptr (fw_shift f 3) in
        let a_3 = mptr (fw_shift f 4) in
        let x_1 = mint (fw_shift f 7) in
        let x_2 = mint (fw_shift f 8) in
        let a_4 = fw_shift a_1 0 in
        let x_3 = 32 + x in
          x = 16384 /\
          FST a = FST a_1 /\
          mptr (fw_shift a_2 4) = f /\
          mptr (fw_shift a_3 3) = f /\
          0 <= x_1 /\
          x_1 < x /\
          0 <= x_2 /\
          x_2 < x /\
          fw_valid_rw malloc f 11 /\
          addr_le a_1 a /\
          fw_p_valid_file malloc mint (fw_shift f 0) /\
          fw_separated f 11 a_3 11 /\
          fw_separated f 11 a_2 11 /\
          fw_separated a_3 11 a_2 11 /\
          fw_p_valid_io_file_pvt_norec
            addr_le addr_lt malloc mptr mint a_3 /\
          fw_p_valid_io_file_pvt_norec
            addr_le addr_lt malloc mptr mint a_2 /\
          fw_valid_rw malloc a_4 x_3 /\
          fw_separated f 11 a_4 x_3 /\
          fw_separated a_3 11 a_4 x_3 /\
          fw_separated a_2 11 a_4 x_3 /\
          addr_lt a (fw_shift a_1 x_3)
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint32 : int -> int.
      !i_3 i_4 : int.
      !a_4 a_5 a_2 a : int # int.
      !t_1 t_2 : (int # int) -> int.
      !i_5 : int.
      !t_3 : (int # int) -> (int # int).
      !t : int -> int.
      !a_1 a_3 : int # int.
      !i i_1 i_2 : int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        (!z : int. fw_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          fw_is_uint32 z ==>
          to_uint32 z = z) ==>
        let x = i_3 + i_4 in
        let data_pointer = t_3 (fw_shift a_5 6) in
        let buffer_pointer = t_3 (fw_shift a_5 5) in
        let previous_file = t_3 (fw_shift a_5 4) in
        let next_file = t_3 (fw_shift a_5 3) in
        let input_bytes = t_1 (fw_shift a_5 7) in
        let write_start = fw_shift a_4 0 in
        let buffer_start = fw_shift buffer_pointer 0 in
        let public_file = fw_shift a_5 0 in
        let updated_t_1 =
          fw_update
            (fw_update
              (fw_update t_1 (fw_shift a_5 8) i)
              (fw_shift public_file 1) i_1)
            (fw_shift public_file 2) i_2
        in
          i_4 <> 0 ==>
          fw_shift a_2 0 = fw_shift a 0 ==>
          t_1 (fw_shift a_5 10) = 1 ==>
          t_1 (fw_shift a_5 9) = 16384 ==>
          FST data_pointer = FST buffer_pointer ==>
          t_3 (fw_shift previous_file 3) = a_5 ==>
          t_3 (fw_shift next_file 4) = a_5 ==>
          t_2 (fw_shift a_4 (to_uint32 (i_4 - 1))) = 10 ==>
          0 <= i ==>
          0 <= i_3 ==>
          0 <= i_4 ==>
          0 <= i_5 ==>
          0 <= x ==>
          0 <= input_bytes ==>
          region (FST a_2) <= 0 ==>
          region (FST a_4) <= 0 ==>
          i <= 16383 ==>
          input_bytes <= 16383 ==>
          fw_framed region t_3 ==>
          linked t ==>
          sconst t_2 ==>
          fw_is_uint32 i ==>
          fw_is_uint32 i_3 ==>
          fw_is_uint32 i_4 ==>
          fw_is_uint32 i_5 ==>
          fw_valid_rw t a_5 11 ==>
          fw_is_uint32 x ==>
          fw_is_uint32 input_bytes ==>
          fw_p_valid_io_file_pvt
            addr_le addr_lt t t_3 t_1 a_1 ==>
          fw_p_valid_io_file_pvt
            addr_le addr_lt t t_3 t_1 a_3 ==>
          fw_p_valid_io_file_pvt
            addr_le addr_lt t t_3 t_1 a_5 ==>
          addr_le buffer_pointer data_pointer ==>
          fw_valid_rw t write_start i_4 ==>
          fw_valid_rw t write_start x ==>
          fw_separated a_5 11 next_file 11 ==>
          fw_separated a_5 11 previous_file 11 ==>
          fw_separated next_file 11 previous_file 11 ==>
          addr_lt data_pointer (fw_shift buffer_pointer 16416) ==>
          fw_valid_rw t buffer_start 16416 ==>
          fw_p_valid_file t updated_t_1 public_file ==>
          fw_separated a_5 11 buffer_start 16416 ==>
          fw_separated next_file 11 buffer_start 16416 ==>
          fw_separated previous_file 11 buffer_start 16416 ==>
          fw_p_valid_io_file_pvt_norec
            addr_le addr_lt t t_3 updated_t_1 next_file ==>
          fw_p_valid_io_file_pvt_norec
            addr_le addr_lt t t_3 updated_t_1 previous_file ==>
          (!i_6 : int.
            i_4 < i_6 ==>
            i_6 <= x ==>
            t_2 (fw_shift a_4 (i_6 - 1)) <> 10) ==>
          fw_p_valid_io_file_pvt
            addr_le addr_lt t t_3 updated_t_1 a_5``;
