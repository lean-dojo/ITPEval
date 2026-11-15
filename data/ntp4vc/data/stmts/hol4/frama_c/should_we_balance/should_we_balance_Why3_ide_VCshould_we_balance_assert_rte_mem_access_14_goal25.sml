(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_14_goal25:
  runtime memory-read validity for a should-we-balance scheduling field under
  modeled address, allocation, havoc, CPU-mask, scheduling, separation, and
  integer-bound conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory int_bitwiseTheory pairTheory;

val goal25 =
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
      !i_1 : int.
      !t_1 t_2 : (int # int) -> int.
      !i_3 i_2 i_4 : int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
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
        (!z : int. swb_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          swb_is_uint32 z ==>
          to_uint32 z = z) ==>
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
        let a_5 = swb_shift a_4 0 in
        let a_6 = t_4 a_5 in
        let a_7 = swb_shift a_1 1 in
        let x_1 = t_3 a_7 in
        let x_2 = t_3 (swb_shift a_6 x_1) in
        let a_8 = swb_shift a_1 0 in
        let a_9 = swb_shift a i_1 in
        let a_10 = t_4 a_8 in
        let a_11 = swb_shift a_10 1 in
        let a_12 = swb_shift a_9 0 in
        let a_13 = swb_shift a_10 0 in
        let a_14 = t_4 a_13 in
        let a_15 = l_group_balance_mask a_14 in
        let a_16 = t_4 a_12 in
        let a_17 = swb_shift a_16 0 in
        let a_18 = swb_shift a_6 0 in
        let a_19 = swb_havoc t_1 t_3 a_17 l_size in
        let a_20 = t_4 (swb_shift a_15 0) in
        let a_21 = swb_havoc t_2 t_3 a_17 l_size in
        let a_22 = a_21 (swb_shift a_16 i_3) in
        let a_23 = a_21 (swb_shift a_6 i_2) in
        let a_24 = a_21 (swb_shift a_6 i_3) in
        let a_25 = a_21 (swb_shift a_20 i_2) in
        let a_26 = a_21 a_11 in
        let a_27 = swb_shift a_20 0 in
        let x_3 = to_uint32 i_4 in
          ~(l_idle_cpu i_3 = 0) ==>
          ~(x = 2) ==>
          ~(x_2 = 0) ==>
          0 <= i_1 ==>
          i_1 < l_size ==>
          0 <= i_3 ==>
          i_3 < l_size ==>
          0 <= i_4 ==>
          i_4 <= l_size ==>
          to_uint32 i_3 < l_size ==>
          0 <= x_1 ==>
          x_1 < l_size ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          swb_framed region t_4 ==>
          linked t ==>
          swb_is_uint32 i_1 ==>
          swb_is_sint32 i_2 ==>
          swb_is_sint32 i_3 ==>
          swb_is_sint32 i_4 ==>
          swb_valid_rd t a_1 5 ==>
          swb_is_uint32 x ==>
          swb_is_sint32 x_1 ==>
          swb_valid_rd t a_3 1 ==>
          swb_valid_rd t a_7 1 ==>
          swb_valid_rd t a_2 1 ==>
          swb_valid_rd t a_8 1 ==>
          swb_valid_rd t a_9 1 ==>
          swb_valid_rd t a_4 1 ==>
          swb_valid_rd t (t_4 (swb_shift a_1 2)) 2 ==>
          swb_valid_rd t a_10 2 ==>
          swb_is_sint32 (t_3 a_11) ==>
          swb_valid_rd t a_12 1 ==>
          swb_valid_rd t a_5 1 ==>
          swb_valid_rd t a_13 1 ==>
          swb_valid_rd t a_14 1 ==>
          swb_valid_rd t a_15 1 ==>
          swb_is_uint8 x_2 ==>
          swb_valid_rd t a_17 l_size ==>
          swb_valid_rd t a_18 l_size ==>
          swb_valid_rw t a_17 l_size ==>
          swb_is_uint8 (a_19 (swb_shift a_6 (-1))) ==>
          swb_is_uint8 (a_19 (swb_shift a_20 (-1))) ==>
          swb_is_uint8 a_22 ==>
          swb_is_uint8 a_23 ==>
          swb_is_uint8 a_24 ==>
          swb_is_uint8 a_25 ==>
          swb_is_sint32 (a_19 a_11) ==>
          swb_is_sint32 a_26 ==>
          swb_valid_rd t a_27 l_size ==>
          swb_separated a_17 l_size a_27 l_size ==>
          (~(int_and 7 a_26 = 0) ==> i_2 = -1) ==>
          (~(i_2 = -1) ==>
            ~(l_idle_cpu i_2 = 0) /\
            ~(a_23 = 0) /\
            ~(a_25 = 0) /\
            0 <= i_2 /\
            i_2 < l_size) ==>
          (i_2 = -1 ==>
            (!i_5 : int.
              ~(a_21 (swb_shift a_20 i_5) = 0) ==>
              0 <= i_5 ==>
              i_5 < l_size ==>
              ~(a_21 (swb_shift a_16 i_5) = 0))) ==>
          ((?i_5 : int.
              ~(a_21 (swb_shift a_16 i_5) = 0) /\
              ~(a_21 (swb_shift a_6 i_5) = 0) /\
              i_5 < l_size /\
              x_3 <= i_5) ==>
            x_3 <= i_3) ==>
          ((?i_5 : int.
              ~(a_21 (swb_shift a_16 i_5) = 0) /\
              ~(a_21 (swb_shift a_6 i_5) = 0) /\
              i_5 < l_size /\
              x_3 <= i_5) ==>
            ~(a_22 = 0) /\ ~(a_24 = 0)) ==>
          ((!i_5 : int.
              i_5 < l_size ==>
              x_3 <= i_5 ==>
              a_21 (swb_shift a_16 i_5) = 0 \/
              a_21 (swb_shift a_6 i_5) = 0) ==>
            l_size = i_3) ==>
          (~(i_2 = -1) ==>
            (!i_5 : int.
              ~(a_21 (swb_shift a_6 i_5) = 0) ==>
              ~(a_21 (swb_shift a_20 i_5) = 0) ==>
              0 <= i_5 ==>
              i_5 < i_2 ==>
              i_5 < l_size ==>
              l_idle_cpu i_5 = 0)) ==>
          (i_2 = -1 ==>
            (!i_5 : int.
              ~(a_21 (swb_shift a_6 i_5) = 0) ==>
              ~(a_21 (swb_shift a_20 i_5) = 0) ==>
              0 <= i_5 ==>
              i_5 < i_4 ==>
              i_5 < l_size ==>
              l_idle_cpu i_5 = 0)) ==>
          ((?i_5 : int.
              ~(a_21 (swb_shift a_16 i_5) = 0) /\
              ~(a_21 (swb_shift a_6 i_5) = 0) /\
              i_5 < l_size /\
              x_3 <= i_5) ==>
            (!i_5 : int.
              i_5 < i_3 ==>
              x_3 <= i_5 ==>
              a_21 (swb_shift a_16 i_5) = 0 \/
              a_21 (swb_shift a_6 i_5) = 0)) ==>
          (~(i_2 = -1) ==>
            (!i_5 : int.
              ~(a_21 (swb_shift a_6 i_5) = 0) ==>
              ~(a_21 (swb_shift a_20 i_5) = 0) ==>
              0 <= i_5 ==>
              i_2 <= i_5 ==>
              i_5 < i_4 ==>
              i_5 < l_size ==>
              ~(swb_idle_core t_4 a_21 i_5))) ==>
          (~(i_2 = -1) ==>
            (!i_5 : int.
              ~(a_21 (swb_shift a_20 i_5) = 0) ==>
              0 <= i_5 ==>
              i_5 < l_size ==>
              ~(a_21 (swb_shift a_16 i_5) = 0) \/
              ~(swb_idle_core t_4 a_21 i_5))) ==>
          (!i_5 : int.
            0 <= i_5 ==>
            i_5 < l_size ==>
            swb_separated
              a_18 l_size
              (swb_shift
                (t_4 (swb_shift (swb_shift a i_5) 0)) 0)
              l_size) ==>
          (!i_5 : int.
            let a_28 = swb_shift a i_5 in
              0 <= i_5 ==>
              i_5 < l_size ==>
              swb_valid_rd t a_28 1 /\
              swb_valid_rw
                t
                (swb_shift (t_4 (swb_shift a_28 0)) 0)
                l_size) ==>
          (!i_5 : int.
            0 <= i_5 ==>
            i_5 < l_size ==>
            (~(a_19 (swb_shift a_20 i_5) = 0) <=>
             ~(a_19 (swb_shift a_16 i_5) = 0))) ==>
          (!i_5 : int.
            ~(a_21 (swb_shift a_16 i_5) = 0) ==>
            0 <= i_5 ==>
            i_5 < l_size ==>
            ~(a_21 (swb_shift a_20 i_5) = 0)) ==>
          (!a_28 : int # int.
            let a_29 = l_sched_group_cpus a_28 in
            let a_30 = swb_shift (t_4 (swb_shift a_29 0)) 0 in
              swb_valid_rd t a_29 1 /\
              swb_valid_rd t a_30 l_size /\
              (!i_5 : int.
                0 <= i_5 ==>
                i_5 < l_size ==>
                swb_separated
                  a_30 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_5) 0)) 0)
                  l_size)) ==>
          (!a_28 : int # int.
            let a_29 = l_sched_group_mask a_28 in
            let a_30 = swb_shift (t_4 (swb_shift a_29 0)) 0 in
              swb_valid_rd t a_29 1 /\
              swb_valid_rd t a_30 l_size /\
              (!i_5 : int.
                0 <= i_5 ==>
                i_5 < l_size ==>
                swb_separated
                  a_30 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_5) 0)) 0)
                  l_size)) ==>
          (!a_28 : int # int.
            let a_29 = l_group_balance_mask a_28 in
            let a_30 = swb_shift (t_4 (swb_shift a_29 0)) 0 in
              swb_valid_rd t a_29 1 /\
              swb_valid_rd t a_30 l_size /\
              (!i_5 : int.
                0 <= i_5 ==>
                i_5 < l_size ==>
                swb_separated
                  a_30 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_5) 0)) 0)
                  l_size)) ==>
          (!i_5 : int.
            let a_28 = l_cpu_smt_mask i_5 in
            let a_29 = swb_shift (t_4 (swb_shift a_28 0)) 0 in
              0 <= i_5 ==>
              i_5 < l_size ==>
              swb_valid_rd t a_28 1 /\
              swb_valid_rd t a_29 l_size /\
              (!i_6 : int.
                0 <= i_6 ==>
                i_6 < l_size ==>
                swb_separated
                  a_29 l_size
                  (swb_shift
                    (t_4 (swb_shift (swb_shift a i_6) 0)) 0)
                  l_size)) ==>
          swb_valid_rd t a_11 1``;
