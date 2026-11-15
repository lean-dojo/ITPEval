(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_10_goal22:
  runtime memory-read validity for a should-we-balance CPU entry under modeled
  address, allocation, havoc, CPU-mask, scheduling, and separation conditions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory int_bitwiseTheory pairTheory;

val goal22 =
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
    let swb_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if swb_separated q 1 p n then m1 q else m0 q
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
      !t_3 : (int # int) -> int.
      !t_4 : (int # int) -> (int # int).
      !a : int # int.
      !i : int.
      !t_1 t_2 : (int # int) -> int.
      !i_1 i_2 : int.
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
        let swb_idle_core =
          \mptr : (int # int) -> (int # int).
           \mint : (int # int) -> int.
           \cpu : int.
            !j : int.
              ~(mint
                  (swb_shift
                    (mptr (swb_shift (l_cpu_smt_mask cpu) 0)) j) = 0) ==>
              0 <= j ==>
              j < l_size ==>
              ~(l_idle_cpu j = 0)
        in
        let a_2 = swb_shift a_1 3 in
        let x = t_3 a_2 in
        let a_3 = swb_shift a_1 4 in
        let a_4 = t_4 a_3 in
        let a_5 = t_4 (swb_shift a_4 0) in
        let a_6 = swb_shift a_1 1 in
        let x_1 = t_3 a_6 in
        let x_2 = t_3 (swb_shift a_5 x_1) in
        let a_7 = swb_shift a_1 0 in
        let a_8 = swb_shift a i in
        let a_9 = t_4 a_7 in
        let a_10 = swb_shift a_9 1 in
        let a_11 = swb_shift a_9 0 in
        let a_12 = t_4 a_11 in
        let a_13 = l_group_balance_mask a_12 in
        let a_14 = swb_shift a_5 0 in
        let a_15 = swb_shift a_8 0 in
        let a_16 = t_4 a_15 in
        let a_17 = swb_shift a_16 0 in
        let a_18 = swb_havoc t_1 t_3 a_17 l_size in
        let a_19 = t_4 (swb_shift a_13 0) in
        let a_20 = swb_havoc t_2 t_3 a_17 l_size in
        let a_21 = a_20 (swb_shift a_5 i_1) in
        let a_22 = a_20 (swb_shift a_19 i_1) in
        let a_23 = a_20 a_10 in
        let a_24 = swb_shift a_19 0 in
          ~(x = 2) ==>
          ~(x_2 = 0) ==>
          0 <= i ==>
          i < l_size ==>
          0 <= i_2 ==>
          i_2 <= l_size ==>
          0 <= x_1 ==>
          x_1 < l_size ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          swb_framed region t_4 ==>
          linked t ==>
          swb_is_uint32 i ==>
          swb_is_sint32 i_1 ==>
          swb_is_sint32 i_2 ==>
          swb_valid_rd t a_1 5 ==>
          swb_is_uint32 x ==>
          swb_is_sint32 x_1 ==>
          swb_valid_rd t a_3 1 ==>
          swb_valid_rd t a_6 1 ==>
          swb_valid_rd t a_2 1 ==>
          swb_valid_rd t a_7 1 ==>
          swb_valid_rd t a_8 1 ==>
          swb_valid_rd t a_4 1 ==>
          swb_valid_rd t (t_4 (swb_shift a_1 2)) 2 ==>
          swb_valid_rd t a_9 2 ==>
          swb_is_sint32 (t_3 a_10) ==>
          swb_valid_rd t a_11 1 ==>
          swb_valid_rd t a_12 1 ==>
          swb_valid_rd t a_13 1 ==>
          swb_is_uint8 x_2 ==>
          swb_valid_rd t a_14 l_size ==>
          swb_valid_rw t a_17 l_size ==>
          swb_is_uint8 (a_18 (swb_shift a_5 (-1))) ==>
          swb_is_uint8 (a_18 (swb_shift a_19 (-1))) ==>
          swb_is_uint8 a_21 ==>
          swb_is_uint8 a_22 ==>
          swb_is_sint32 (a_18 a_10) ==>
          swb_is_sint32 a_23 ==>
          swb_valid_rd t a_24 l_size ==>
          swb_separated a_17 l_size a_24 l_size ==>
          (~(int_and 7 a_23 = 0) ==> i_1 = -1) ==>
          (~(i_1 = -1) ==>
            ~(l_idle_cpu i_1 = 0) /\
            ~(a_21 = 0) /\
            ~(a_22 = 0) /\
            0 <= i_1 /\
            i_1 < l_size) ==>
          (i_1 = -1 ==>
            (!i_3 : int.
              ~(a_20 (swb_shift a_19 i_3) = 0) ==>
              0 <= i_3 ==>
              i_3 < l_size ==>
              ~(a_20 (swb_shift a_16 i_3) = 0))) ==>
          (~(i_1 = -1) ==>
            (!i_3 : int.
              ~(a_20 (swb_shift a_5 i_3) = 0) ==>
              ~(a_20 (swb_shift a_19 i_3) = 0) ==>
              0 <= i_3 ==>
              i_3 < i_1 ==>
              i_3 < l_size ==>
              l_idle_cpu i_3 = 0)) ==>
          (i_1 = -1 ==>
            (!i_3 : int.
              ~(a_20 (swb_shift a_5 i_3) = 0) ==>
              ~(a_20 (swb_shift a_19 i_3) = 0) ==>
              0 <= i_3 ==>
              i_3 < i_2 ==>
              i_3 < l_size ==>
              l_idle_cpu i_3 = 0)) ==>
          (~(i_1 = -1) ==>
            (!i_3 : int.
              ~(a_20 (swb_shift a_5 i_3) = 0) ==>
              ~(a_20 (swb_shift a_19 i_3) = 0) ==>
              0 <= i_3 ==>
              i_1 <= i_3 ==>
              i_3 < i_2 ==>
              i_3 < l_size ==>
              ~(swb_idle_core t_4 a_20 i_3))) ==>
          (~(i_1 = -1) ==>
            (!i_3 : int.
              ~(a_20 (swb_shift a_19 i_3) = 0) ==>
              0 <= i_3 ==>
              i_3 < l_size ==>
              ~(a_20 (swb_shift a_16 i_3) = 0) \/
              ~(swb_idle_core t_4 a_20 i_3))) ==>
          (!i_3 : int.
            0 <= i_3 ==>
            i_3 < l_size ==>
            swb_separated
              a_14 l_size
              (swb_shift
                (t_4 (swb_shift (swb_shift a i_3) 0)) 0)
              l_size) ==>
          (!i_3 : int.
            let a_25 = swb_shift a i_3 in
              0 <= i_3 ==>
              i_3 < l_size ==>
              swb_valid_rd t a_25 1 /\
              swb_valid_rw
                t
                (swb_shift (t_4 (swb_shift a_25 0)) 0)
                l_size) ==>
          (!i_3 : int.
            0 <= i_3 ==>
            i_3 < l_size ==>
            (~(a_18 (swb_shift a_19 i_3) = 0) <=>
             ~(a_18 (swb_shift a_16 i_3) = 0))) ==>
          (!i_3 : int.
            ~(a_20 (swb_shift a_16 i_3) = 0) ==>
            0 <= i_3 ==>
            i_3 < l_size ==>
            ~(a_20 (swb_shift a_19 i_3) = 0)) ==>
          (!a_25 : int # int.
            let a_26 = l_sched_group_cpus a_25 in
            let a_27 = swb_shift (t_4 (swb_shift a_26 0)) 0 in
              swb_valid_rd t a_26 1 /\
              swb_valid_rd t a_27 l_size /\
              (!i_3 : int.
                0 <= i_3 ==>
                i_3 < l_size ==>
                swb_separated
                  a_27 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_3) 0)) 0)
                  l_size)) ==>
          (!a_25 : int # int.
            let a_26 = l_sched_group_mask a_25 in
            let a_27 = swb_shift (t_4 (swb_shift a_26 0)) 0 in
              swb_valid_rd t a_26 1 /\
              swb_valid_rd t a_27 l_size /\
              (!i_3 : int.
                0 <= i_3 ==>
                i_3 < l_size ==>
                swb_separated
                  a_27 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_3) 0)) 0)
                  l_size)) ==>
          (!a_25 : int # int.
            let a_26 = l_group_balance_mask a_25 in
            let a_27 = swb_shift (t_4 (swb_shift a_26 0)) 0 in
              swb_valid_rd t a_26 1 /\
              swb_valid_rd t a_27 l_size /\
              (!i_3 : int.
                0 <= i_3 ==>
                i_3 < l_size ==>
                swb_separated
                  a_27 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_3) 0)) 0)
                  l_size)) ==>
          (!i_3 : int.
            let a_25 = l_cpu_smt_mask i_3 in
            let a_26 = swb_shift (t_4 (swb_shift a_25 0)) 0 in
              0 <= i_3 ==>
              i_3 < l_size ==>
              swb_valid_rd t a_25 1 /\
              swb_valid_rd t a_26 l_size /\
              (!i_4 : int.
                0 <= i_4 ==>
                i_4 < l_size ==>
                swb_separated
                  a_26 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_4) 0)) 0)
                  l_size)) ==>
          swb_valid_rd t a_15 1``;
