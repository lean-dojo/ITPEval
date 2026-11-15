(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_3_goal17:
  updating the first free allocation marker in a modeled Contiki memb structure
  decreases its free-marker occurrence count by one. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal17 =
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
    let ma_occ_axioms =
      \l_occ :
        (((int # int) -> int) ->
         int -> (int # int) -> int -> int -> int).
        (!to from mchar e base.
          to <= from ==>
          l_occ mchar e base from to = 0) /\
        (!to mchar base e from.
          mchar (ma_shift base (to - 1)) = e ==>
          from < to ==>
          1 + l_occ mchar e base from (to - 1) =
          l_occ mchar e base from to) /\
        (!to mchar base e from.
          mchar (ma_shift base (to - 1)) <> e ==>
          from < to ==>
          l_occ mchar e base from (to - 1) =
          l_occ mchar e base from to)
    in
    let ma_numfree =
      \l_occ :
        (((int # int) -> int) ->
         int -> (int # int) -> int -> int -> int).
       \mptr : (int # int) -> (int # int).
       \mchar : (int # int) -> int.
       \mint : (int # int) -> int.
       \memb : int # int.
        l_occ mchar 0 (mptr (ma_shift memb 2)) 0
          (mint (ma_shift memb 1))
    in
      !l_occ :
        (((int # int) -> int) ->
         int -> (int # int) -> int -> int -> int).
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
        ma_occ_axioms l_occ ==>
        !a : int # int.
        !t_4 : (int # int) -> (int # int).
        !t_1 : (int # int) -> int.
        !i_2 : int.
        !t_2 : (int # int) -> int.
        !i i_1 : int.
        !t : int -> int.
        !t_3 : (int # int) -> int.
          let a_1 = ma_shift a 2 in
          let a_2 = t_4 a_1 in
          let a_3 = ma_shift a 1 in
          let x = t_1 a_3 in
          let a_4 = ma_shift a 0 in
          let x_1 = t_1 a_4 in
          let a_5 = ma_shift a_2 i_2 in
          let x_2 = i_2 * x_1 in
            t_2 (ma_shift a_2 i) = 0 ==>
            0 <= i ==>
            0 <= i_1 ==>
            i < x ==>
            i_1 <= x ==>
            region (FST a) <= 0 ==>
            ma_framed region t_4 ==>
            linked t ==>
            sconst t_2 ==>
            ma_is_sint32 i_1 ==>
            ma_is_sint32 i_2 ==>
            ma_is_uint16 x ==>
            ma_is_uint16 x_1 ==>
            ma_p_valid_memb t t_4 t_1 a ==>
            ma_valid_rd t a_3 1 ==>
            (if i_1 < x then
               i_2 = i_1 /\
               t_2 a_5 = 0 /\
               ma_update t_2 a_5 1 = t_3 /\
               -2147483648 <= x_2 /\
               x_2 <= 2147483647 /\
               ma_valid_rd t a_1 1 /\
               ma_valid_rd t (ma_shift a 3) 1 /\
               ma_valid_rd t a_4 1 /\
               ma_valid_rd t a_5 1 /\
               ma_valid_rw t a_5 1
             else
               t_3 = t_2) ==>
            (!i_3 : int.
              0 <= i_3 ==>
              i_3 < i_1 ==>
              ~(t_2 (ma_shift a_2 i_3) = 0)) ==>
            1 + ma_numfree l_occ t_4 t_3 t_1 a =
            ma_numfree l_occ t_4 t_2 t_1 a``;
