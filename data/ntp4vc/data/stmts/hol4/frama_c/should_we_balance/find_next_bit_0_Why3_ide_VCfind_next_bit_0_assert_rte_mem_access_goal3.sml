(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/find_next_bit_0_Why3_ide_VCfind_next_bit_0_assert_rte_mem_access_goal3:
  memory-access validity for reading the next byte in the modeled
  find-next-bit scan. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal3 =
  ``let fnb_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let fnb_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let fnb_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let fnb_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
      !a : int # int.
      !i_2 i i_1 : int.
      !t : int -> int.
      !t_1 : (int # int) -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !l_size : int.
        0 < l_size /\ l_size <= 2147483647 ==>
        let a_1 = fnb_shift a i_2 in
          i_2 < i ==>
          i_1 <= i_2 ==>
          i <= l_size ==>
          region (FST a) <= 0 ==>
          linked t ==>
          fnb_is_uint32 i ==>
          fnb_is_uint32 i_1 ==>
          fnb_is_uint32 i_2 ==>
          fnb_is_uint8 (t_1 a_1) ==>
          fnb_valid_rd t (fnb_shift a 0) i ==>
          (!i_3 : int.
            i_1 <= i_3 ==>
            i_3 < i_2 ==>
            t_1 (fnb_shift a i_3) = 0) ==>
          fnb_valid_rd t a_1 1``;
