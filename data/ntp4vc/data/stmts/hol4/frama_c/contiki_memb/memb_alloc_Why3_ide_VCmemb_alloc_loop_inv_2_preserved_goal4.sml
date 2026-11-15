(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_loop_inv_2_preserved_goal4:
  preservation of the nonzero allocation-marker loop invariant at an earlier
  index in a modeled Contiki memb structure. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal4 =
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
    let ma_is_sint8 =
      \z : int. -128 <= z /\ z < 128
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
      !a : int # int.
      !t_3 : (int # int) -> (int # int).
      !i : int.
      !t_2 t_1 : (int # int) -> int.
      !i_1 : int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
        let a_1 = ma_shift a 2 in
        let a_2 = t_3 a_1 in
        let a_3 = ma_shift a_2 i in
        let x = t_2 a_3 in
        let a_4 = ma_shift a 1 in
        let x_1 = t_1 a_4 in
          ~(x = 0) ==>
          0 <= i ==>
          i_1 <= i ==>
          0 <= i_1 ==>
          i < x_1 ==>
          i <= x_1 ==>
          region (FST a) <= 0 ==>
          i <= 2147483646 ==>
          ma_framed region t_3 ==>
          linked t ==>
          sconst t_2 ==>
          ma_is_sint32 i ==>
          ma_is_sint32 i_1 ==>
          ma_is_uint16 x_1 ==>
          ma_is_sint32 (1 + i) ==>
          ma_p_valid_memb t t_3 t_1 a ==>
          ma_valid_rd t a_1 1 ==>
          ma_valid_rd t a_4 1 ==>
          ma_is_sint8 x ==>
          ma_valid_rd t a_3 1 ==>
          (!i_2 : int.
            0 <= i_2 ==>
            i_2 < i ==>
            ~(t_2 (ma_shift a_2 i_2) = 0)) ==>
          ~(t_2 (ma_shift a_2 i_1) = 0)``;
