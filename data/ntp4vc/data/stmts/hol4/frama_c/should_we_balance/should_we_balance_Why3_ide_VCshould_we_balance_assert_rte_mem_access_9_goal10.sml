(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_9_goal10:
  runtime memory-read validity at the one-unit offset of a pointer loaded from
  the two-unit field of a modeled should-we-balance object, under allocation,
  framing, CPU-mask, scheduling, separation, and integer-bound conditions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal10 =
  ``let swb_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let swb_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let swb_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let swb_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let swb_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let swb_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let swb_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let swb_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !a_1 : int # int.
      !t_2 : (int # int) -> (int # int).
      !t_1 : (int # int) -> int.
      !i : int.
      !a : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !l_size : int.
      !l_idle_cpu : int -> int.
      !l_sched_group_cpus : (int # int) -> (int # int).
      !l_sched_group_mask : (int # int) -> (int # int).
      !l_group_balance_mask : (int # int) -> (int # int).
      !l_cpu_smt_mask : int -> (int # int).
        let swb_mask_member =
          \mint : (int # int) -> int.
           \mptr : (int # int) -> (int # int).
           \cpu : int. \member : int.
            ~(mint
                (swb_shift
                  (mptr (swb_shift (l_cpu_smt_mask cpu) 0))
                  member) = 0)
        in
        0 < l_size /\ l_size <= 2147483647 ==>
        (!cpu : int. swb_is_uint8 (l_idle_cpu cpu)) ==>
        (!i : int.
         !mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
           0 <= i ==>
           i < l_size ==>
           swb_mask_member mint mptr i i) ==>
        (!mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
         !j i : int.
           swb_mask_member mint mptr j i ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           swb_mask_member mint mptr i j) ==>
        (!mptr : (int # int) -> (int # int).
         !i : int.
         !mint : (int # int) -> int.
         !j k : int.
           swb_mask_member mint mptr i j ==>
           swb_mask_member mint mptr j k ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           0 <= k ==>
           k < l_size ==>
           swb_mask_member mint mptr i k) ==>
        let a_2 = swb_shift a_1 3 in
        let a_3 = swb_shift a_1 4 in
        let a_4 = t_2 a_3 in
        let a_5 = t_2 (swb_shift a_4 0) in
        let a_6 = swb_shift a_1 1 in
        let x = t_1 a_6 in
        let x_1 = t_1 (swb_shift a_5 x) in
        let a_7 = swb_shift a_1 2 in
        let a_8 = t_2 a_7 in
        let a_9 = swb_shift a_8 0 in
        let x_2 = t_1 a_9 in
        let a_10 = swb_shift a_1 0 in
        let a_11 = t_2 a_10 in
        let a_12 = swb_shift a_8 1 in
        let a_13 = swb_shift a_11 0 in
        let a_14 = swb_shift a_5 0 in
          t_1 a_2 = 2 ==>
          ~(x_1 = 0) ==>
          0 <= i ==>
          i < l_size ==>
          0 <= x ==>
          x < l_size ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          x_2 <= 0 ==>
          swb_framed region t_2 ==>
          linked t ==>
          swb_is_uint32 i ==>
          swb_valid_rd t a_1 5 ==>
          swb_is_sint32 x ==>
          swb_valid_rd t a_3 1 ==>
          swb_valid_rd t a_6 1 ==>
          swb_valid_rd t a_7 1 ==>
          swb_valid_rd t a_2 1 ==>
          swb_valid_rd t a_10 1 ==>
          swb_valid_rd t a_4 1 ==>
          swb_valid_rd t a_8 2 ==>
          swb_valid_rd t a_11 2 ==>
          swb_is_uint32 x_2 ==>
          swb_is_uint32 (t_1 a_12) ==>
          swb_is_sint32 (t_1 (swb_shift a_11 1)) ==>
          swb_valid_rd t a_13 1 ==>
          swb_valid_rd t a_9 1 ==>
          swb_valid_rd t (t_2 a_13) 1 ==>
          swb_is_uint8 x_1 ==>
          swb_valid_rd t a_14 l_size ==>
          (!i_1 : int.
            0 <= i_1 ==>
            i_1 < l_size ==>
            swb_separated
              a_14 l_size
              (swb_shift
                (t_2 (swb_shift (swb_shift a i_1) 0)) 0)
              l_size) ==>
          (!i_1 : int.
            let a_15 = swb_shift a i_1 in
              0 <= i_1 ==>
              i_1 < l_size ==>
              swb_valid_rd t a_15 1 /\
              swb_valid_rw
                t
                (swb_shift (t_2 (swb_shift a_15 0)) 0)
                l_size) ==>
          (!a_15 : int # int.
            let a_16 = l_sched_group_cpus a_15 in
            let a_17 = swb_shift (t_2 (swb_shift a_16 0)) 0 in
              swb_valid_rd t a_16 1 /\
              swb_valid_rd t a_17 l_size /\
              (!i_1 : int.
                0 <= i_1 ==>
                i_1 < l_size ==>
                swb_separated
                  a_17 l_size
                  (swb_shift
                    (t_2 (swb_shift (swb_shift a i_1) 0)) 0)
                  l_size)) ==>
          (!a_15 : int # int.
            let a_16 = l_sched_group_mask a_15 in
            let a_17 = swb_shift (t_2 (swb_shift a_16 0)) 0 in
              swb_valid_rd t a_16 1 /\
              swb_valid_rd t a_17 l_size /\
              (!i_1 : int.
                0 <= i_1 ==>
                i_1 < l_size ==>
                swb_separated
                  a_17 l_size
                  (swb_shift
                    (t_2 (swb_shift (swb_shift a i_1) 0)) 0)
                  l_size)) ==>
          (!a_15 : int # int.
            let a_16 = l_group_balance_mask a_15 in
            let a_17 = swb_shift (t_2 (swb_shift a_16 0)) 0 in
              swb_valid_rd t a_16 1 /\
              swb_valid_rd t a_17 l_size /\
              (!i_1 : int.
                0 <= i_1 ==>
                i_1 < l_size ==>
                swb_separated
                  a_17 l_size
                  (swb_shift
                    (t_2 (swb_shift (swb_shift a i_1) 0)) 0)
                  l_size)) ==>
          (!i_1 : int.
            let a_15 = l_cpu_smt_mask i_1 in
            let a_16 = swb_shift (t_2 (swb_shift a_15 0)) 0 in
              0 <= i_1 ==>
              i_1 < l_size ==>
              swb_valid_rd t a_15 1 /\
              swb_valid_rd t a_16 l_size /\
              (!i_2 : int.
                0 <= i_2 ==>
                i_2 < l_size ==>
                swb_separated
                  a_16 l_size
                  (swb_shift
                    (t_2 (swb_shift (swb_shift a i_2) 0)) 0)
                  l_size)) ==>
          swb_valid_rd t a_12 1``;
