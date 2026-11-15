(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_assert_rte_mem_access_4_goal11:
  memory-access validity for reading the pointer field at offset two of a
  modeled Contiki memb structure during deallocation. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val memb_free_Why3_ide_VCmemb_free_assert_rte_mem_access_4_goal11 =
  ``let ma_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ma_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ma_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ma_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let ma_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ma_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ma_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
    let ma_p_valid_memb =
      \malloc : int -> int.
       \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \memb : int # int.
        let size = mint (ma_shift memb 0) in
        let count = mint (ma_shift memb 1) in
        let total = count * size in
        let used = mptr (ma_shift memb 2) in
        let mem = mptr (ma_shift memb 3) in
        let used_start = ma_shift used 0 in
        let mem_start = ma_shift mem 0 in
          0 < size /\
          total <= 2147483647 /\
          ma_valid_rw malloc memb 4 /\
          ma_valid_rw malloc used 1 /\
          ma_valid_rw malloc mem 1 /\
          ma_valid_rw malloc used_start count /\
          ma_valid_rw malloc mem_start total /\
          ma_separated used_start count mem_start total
    in
    let ma_memb_index =
      \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \memb : int # int.
       \ptr : int # int.
        (SND ptr - SND (mptr (ma_shift memb 3))) quot
          mint (ma_shift memb 0)
    in
    let ma_memb_ptr =
      \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \memb : int # int.
       \index : int.
        ma_shift (mptr (ma_shift memb 3))
          (index * mint (ma_shift memb 0))
    in
      !t_3 : (int # int) -> (int # int).
      !t_1 : (int # int) -> int.
      !a_1 a : int # int.
      !t : int -> int.
      !t_2 : (int # int) -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
        let x = ma_memb_index t_3 t_1 a_1 a in
        let a_2 = ma_shift a_1 1 in
        let x_1 = t_1 a_2 in
        let a_3 = ma_shift a_1 3 in
          ma_memb_ptr t_3 t_1 a_1 x = a ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          0 <= x ==>
          x < x_1 ==>
          x <= x_1 ==>
          ma_framed region t_3 ==>
          linked t ==>
          sconst t_2 ==>
          ma_is_uint16 x_1 ==>
          ma_p_valid_memb t t_3 t_1 a_1 ==>
          ma_valid_rd t a_3 1 ==>
          ma_valid_rd t a_2 1 ==>
          ma_is_sint32 x ==>
          (!i : int.
            0 <= i ==>
            i < x ==>
            ~(ma_shift (t_3 a_3)
              (i * t_1 (ma_shift a_1 0)) = a)) ==>
          ma_valid_rd t (ma_shift a_1 2) 1``;
