(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_loop_inv_2_preserved_goal3:
  preservation of the idle-CPU loop invariant under modeled CPU SMT masks,
  address arithmetic, memory validity, separation, framing, and integer
  bounds. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal3 =
  ``let icp_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let icp_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let icp_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let icp_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let icp_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let icp_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let icp_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let icp_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !i_5 : int.
      !t_2 : (int # int) -> (int # int).
      !t_1 : (int # int) -> int.
      !i_4 i_2 i_3 i i_1 : int.
      !a : int # int.
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
        let icp_mask_member =
          \mint : (int # int) -> int.
           \mptr : (int # int) -> (int # int).
           \cpu : int. \member : int.
            ~(mint
                (icp_shift
                  (mptr (icp_shift (l_cpu_smt_mask cpu) 0))
                  member) = 0)
        in
        0 < l_size /\ l_size <= 2147483647 ==>
        (!cpu : int. icp_is_uint8 (l_idle_cpu cpu)) ==>
        (!i : int.
         !mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
           0 <= i ==>
           i < l_size ==>
           icp_mask_member mint mptr i i) ==>
        (!mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
         !j i : int.
           icp_mask_member mint mptr j i ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           icp_mask_member mint mptr i j) ==>
        (!mptr : (int # int) -> (int # int).
         !i : int.
         !mint : (int # int) -> int.
         !j k : int.
           icp_mask_member mint mptr i j ==>
           icp_mask_member mint mptr j k ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           0 <= k ==>
           k < l_size ==>
           icp_mask_member mint mptr i k) ==>
        (!z : int. icp_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          icp_is_uint32 z ==>
          to_uint32 z = z) ==>
        let a_1 = icp_shift (l_cpu_smt_mask i_5) 0 in
        let a_2 = t_2 a_1 in
        let x = t_1 (icp_shift a_2 i_4) in
        let x_1 = to_uint32 i_2 in
          ~(l_idle_cpu i_5 = 0) ==>
          ~(t_1 (icp_shift a_2 i_3) = 0) ==>
          0 <= i ==>
          i < l_size ==>
          i_3 <= i_1 ==>
          0 <= i_2 ==>
          0 <= i_3 ==>
          0 <= i_5 ==>
          i_5 < l_size ==>
          i_2 <= l_size ==>
          to_uint32 i_4 < l_size ==>
          region (FST a) <= 0 ==>
          icp_framed region t_2 ==>
          linked t ==>
          icp_is_uint32 i ==>
          icp_is_sint32 i_1 ==>
          icp_is_sint32 i_2 ==>
          icp_is_sint32 i_4 ==>
          icp_is_sint32 i_5 ==>
          icp_is_sint32 (1 + i_1) ==>
          icp_valid_rd t a_1 1 ==>
          icp_is_uint8 x ==>
          icp_valid_rd t (icp_shift a_2 0) l_size ==>
          (if i_5 = i_4 then
             i_5 = i_1 /\ i_5 <= 2147483646
           else
             i_4 = i_1 /\
             ~(l_idle_cpu i_4 = 0) /\
             0 <= i_4 /\
             i_4 < l_size /\
             i_4 <= 2147483646) ==>
          ((!i_6 : int.
              i_6 < l_size ==>
              x_1 <= i_6 ==>
              t_1 (icp_shift a_2 i_6) = 0) ==>
            l_size = i_4) ==>
          ((?i_6 : int.
              ~(t_1 (icp_shift a_2 i_6) = 0) /\
              i_6 < l_size /\
              x_1 <= i_6) ==>
            ~(x = 0)) ==>
          ((?i_6 : int.
              ~(t_1 (icp_shift a_2 i_6) = 0) /\
              i_6 < l_size /\
              x_1 <= i_6) ==>
            i_4 < l_size) ==>
          ((?i_6 : int.
              ~(t_1 (icp_shift a_2 i_6) = 0) /\
              i_6 < l_size /\
              x_1 <= i_6) ==>
            i_4 < l_size /\ x_1 <= i_4) ==>
          ((?i_6 : int.
              ~(t_1 (icp_shift a_2 i_6) = 0) /\
              i_6 < l_size /\
              x_1 <= i_6) ==>
            (!i_6 : int.
              i_6 < i_4 ==>
              x_1 <= i_6 ==>
              t_1 (icp_shift a_2 i_6) = 0)) ==>
          (!i_6 : int.
            ~(t_1 (icp_shift a_2 i_6) = 0) ==>
            0 <= i_6 ==>
            i_6 < i_2 ==>
            ~(l_idle_cpu i_6 = 0)) ==>
          (!i_6 : int.
            let a_3 = icp_shift a i_6 in
              0 <= i_6 ==>
              i_6 < l_size ==>
              icp_valid_rd t a_3 1 /\
              icp_valid_rw
                t
                (icp_shift (t_2 (icp_shift a_3 0)) 0)
                l_size) ==>
          (!a_3 : int # int.
            let a_4 = l_sched_group_cpus a_3 in
            let a_5 = icp_shift (t_2 (icp_shift a_4 0)) 0 in
              icp_valid_rd t a_4 1 /\
              icp_valid_rd t a_5 l_size /\
              (!i_6 : int.
                0 <= i_6 ==>
                i_6 < l_size ==>
                icp_separated
                  a_5 l_size
                  (icp_shift
                    (t_2 (icp_shift (icp_shift a i_6) 0)) 0)
                  l_size)) ==>
          (!a_3 : int # int.
            let a_4 = l_sched_group_mask a_3 in
            let a_5 = icp_shift (t_2 (icp_shift a_4 0)) 0 in
              icp_valid_rd t a_4 1 /\
              icp_valid_rd t a_5 l_size /\
              (!i_6 : int.
                0 <= i_6 ==>
                i_6 < l_size ==>
                icp_separated
                  a_5 l_size
                  (icp_shift
                    (t_2 (icp_shift (icp_shift a i_6) 0)) 0)
                  l_size)) ==>
          (!a_3 : int # int.
            let a_4 = l_group_balance_mask a_3 in
            let a_5 = icp_shift (t_2 (icp_shift a_4 0)) 0 in
              icp_valid_rd t a_4 1 /\
              icp_valid_rd t a_5 l_size /\
              (!i_6 : int.
                0 <= i_6 ==>
                i_6 < l_size ==>
                icp_separated
                  a_5 l_size
                  (icp_shift
                    (t_2 (icp_shift (icp_shift a i_6) 0)) 0)
                  l_size)) ==>
          (!i_6 : int.
            let a_3 = l_cpu_smt_mask i_6 in
            let a_4 = icp_shift (t_2 (icp_shift a_3 0)) 0 in
              0 <= i_6 ==>
              i_6 < l_size ==>
              icp_valid_rd t a_3 1 /\
              icp_valid_rd t a_4 l_size /\
              (!i_7 : int.
                0 <= i_7 ==>
                i_7 < l_size ==>
                icp_separated
                  a_4 l_size
                  (icp_shift
                    (t_2 (icp_shift (icp_shift a i_7) 0)) 0)
                  l_size)) ==>
          ~(l_idle_cpu i_3 = 0)``;
