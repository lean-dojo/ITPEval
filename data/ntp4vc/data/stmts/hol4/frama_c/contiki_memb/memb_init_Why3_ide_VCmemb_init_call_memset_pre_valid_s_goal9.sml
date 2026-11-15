(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_call_memset_pre_valid_s_goal9:
  a Contiki memb-initialization verification condition concluding that the
  pointer stored in the third structure field is valid or empty for the block
  count stored in the second field. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal9 =
  ``let mi_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mi_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mi_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mi_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let mi_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let mi_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
    let mi_p_valid_memb =
      \malloc : int -> int.
       \mptr : (int # int) -> (int # int).
       \mint : (int # int) -> int.
       \memb : int # int.
        let size = mint (mi_shift memb 0) in
        let count = mint (mi_shift memb 1) in
        let total = count * size in
        let used = mptr (mi_shift memb 2) in
        let mem = mptr (mi_shift memb 3) in
        let used_start = mi_shift used 0 in
        let mem_start = mi_shift mem 0 in
          0 < size /\
          total <= 2147483647 /\
          mi_valid_rw malloc memb 4 /\
          mi_valid_rw malloc used 1 /\
          mi_valid_rw malloc mem 1 /\
          mi_valid_rw malloc used_start count /\
          mi_valid_rw malloc mem_start total /\
          mi_separated used_start count mem_start total
    in
    let mi_p_empty_block =
      \malloc : int -> int. \s : int # int.
        malloc (FST s) = 0 /\ SND s = 0
    in
    let mi_p_valid_or_empty =
      \malloc : int -> int. \s : int # int. \n : int.
        mi_valid_rw malloc (mi_shift s 0) n /\
        (mi_p_empty_block malloc s \/ mi_valid_rd malloc s 1)
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !a : int # int.
      !t_1 : (int # int) -> int.
      !t_3 : (int # int) -> (int # int).
      !t : int -> int.
      !t_2 : (int # int) -> int.
        let a_1 = mi_shift a 1 in
        let x = t_1 a_1 in
        let a_2 = mi_shift a 2 in
          region (FST a) <= 0 ==>
          mi_framed region t_3 ==>
          linked t ==>
          sconst t_2 ==>
          mi_is_uint16 x ==>
          mi_is_uint16 (t_1 (mi_shift a 0)) ==>
          mi_p_valid_memb t t_3 t_1 a ==>
          mi_valid_rd t a_2 1 ==>
          mi_valid_rd t a_1 1 ==>
          mi_p_valid_or_empty t (t_3 a_2) x``;
