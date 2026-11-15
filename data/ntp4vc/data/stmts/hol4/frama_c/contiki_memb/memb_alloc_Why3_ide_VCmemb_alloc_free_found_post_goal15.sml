(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_goal15:
  existence of the first free allocation slot, its returned address, and
  preservation of all other allocation markers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal15 =
  ``let ma_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ma_update =
      \f : (int # int) -> int.
       \p : int # int.
       \v : int.
       \q : int # int.
        if q = p then v else f q
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
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !a_1 : int # int.
      !t_4 : (int # int) -> (int # int).
      !t_1 : (int # int) -> int.
      !i_2 : int.
      !t_3 : (int # int) -> int.
      !i i_1 : int.
      !t : int -> int.
      !t_2 : (int # int) -> int.
      !a : int # int.
        let a_2 = ma_shift a_1 2 in
        let a_3 = t_4 a_2 in
        let a_4 = ma_shift a_1 1 in
        let x = t_1 a_4 in
        let a_5 = ma_shift a_1 0 in
        let x_1 = t_1 a_5 in
        let a_6 = ma_shift a_3 i_2 in
        let a_7 = ma_shift a_1 3 in
        let a_8 = t_4 a_7 in
        let x_2 = i_2 * x_1 in
          t_3 (ma_shift a_3 i) = 0 ==>
          0 <= i ==>
          0 <= i_1 ==>
          i < x ==>
          i_1 <= x ==>
          region (FST a_1) <= 0 ==>
          ma_framed region t_4 ==>
          linked t ==>
          sconst t_3 ==>
          ma_is_sint32 i_1 ==>
          ma_is_sint32 i_2 ==>
          ma_is_uint16 x ==>
          ma_is_uint16 x_1 ==>
          ma_p_valid_memb t t_4 t_1 a_1 ==>
          ma_valid_rd t a_4 1 ==>
          (if i_1 < x then
             i_2 = i_1 /\
             t_3 a_6 = 0 /\
             ma_update t_3 a_6 1 = t_2 /\
             ma_shift a_8 x_2 = a /\
             -2147483648 <= x_2 /\
             x_2 <= 2147483647 /\
             ma_valid_rd t a_2 1 /\
             ma_valid_rd t a_7 1 /\
             ma_valid_rd t a_5 1 /\
             ma_valid_rd t a_6 1 /\
             ma_valid_rw t a_6 1
           else
             t_3 = t_2 /\ (0, 0) = a) ==>
          (!i_3 : int.
            0 <= i_3 ==>
            i_3 < i_1 ==>
            ~(t_3 (ma_shift a_3 i_3) = 0)) ==>
          ?i_3 : int.
            let a_9 = ma_shift a_3 i_3 in
              t_2 a_9 = 1 /\
              t_3 a_9 = 0 /\
              ma_shift a_8 (i_3 * x_1) = a /\
              0 <= i_3 /\
              i_3 < x /\
              (!i_4 : int.
                let a_10 = ma_shift a_3 i_4 in
                  ((0 <= i_4 /\ i_4 < i_3) \/
                   (i_3 < i_4 /\ i_4 < x)) ==>
                  t_3 a_10 = t_2 a_10)``;
