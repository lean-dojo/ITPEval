(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_not_newly_idle_with_idle_post_2_goal35:
  the should-we-balance postcondition equating the selected CPU index test
  with a nonzero Boolean result, under non-newly-idle and nonzero idle-mask
  hypotheses plus modeled memory, exact unsigned and bitwise operations,
  CPU-mask invariants, idle-core, havoc, separation, framing, and integer-bound
  conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory int_bitwiseTheory pairTheory;

val goal35 =
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
    let swb_to_uint32 =
      \z : int. z % 4294967296
    in
      !a_1 : int # int.
      !t_7 : (int # int) -> int.
      !t_8 : (int # int) -> (int # int).
      !a : int # int.
      !i : int.
      !t_6 : (int # int) -> int.
      !i_8 i_3 i_9 : int.
      !t_5 : (int # int) -> int.
      !i_5 i_6 : int.
      !t : int -> int.
      !i_1 i_2 i_4 i_7 i_10 : int.
      !t_4 t_1 t_2 t_3 : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !l_size : int.
      !l_idle_cpu : int -> int.
      !l_sched_group_cpus : (int # int) -> (int # int).
      !l_sched_group_mask : (int # int) -> (int # int).
      !l_group_balance_mask : (int # int) -> (int # int).
      !l_group_balance_cpu : (int # int) -> int.
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
              swb_mask_member mint mptr cpu j ==>
              0 <= j ==>
              j < l_size ==>
              ~(l_idle_cpu j = 0)
        in
        let a_2 = swb_shift a_1 3 in
        let x = t_7 a_2 in
        let a_3 = swb_shift a_1 0 in
        let a_4 = t_8 a_3 in
        let a_5 = swb_shift a_4 1 in
        let x_1 = t_7 a_5 in
        let a_6 = swb_shift a_1 4 in
        let a_7 = t_8 a_6 in
        let a_8 = swb_shift a_7 0 in
        let a_9 = t_8 a_8 in
        let a_10 = swb_shift a_1 1 in
        let x_2 = t_7 a_10 in
        let x_3 = t_7 (swb_shift a_9 x_2) in
        let a_11 = swb_shift a_4 0 in
        let a_12 = t_8 a_11 in
        let a_13 = l_group_balance_mask a_12 in
        let a_14 = t_8 (swb_shift a_13 0) in
        let a_15 = swb_shift a i in
        let a_16 = swb_shift a_15 0 in
        let a_17 = t_8 a_16 in
        let a_18 = swb_shift a_17 0 in
        let a_19 = swb_shift a_9 0 in
        let a_20 = swb_havoc t_6 t_7 a_18 l_size in
        let a_21 = a_20 (swb_shift a_17 i_8) in
        let a_22 = a_20 (swb_shift a_9 i_3) in
        let a_23 = a_20 (swb_shift a_9 i_8) in
        let a_24 = a_20 (swb_shift a_14 i_3) in
        let a_25 = a_20 a_5 in
        let a_26 = swb_shift a_14 0 in
        let a_27 = a_20 a_10 in
        let x_4 = int_and 7 a_25 in
        let x_5 = swb_to_uint32 i_9 in
        let a_28 = swb_havoc t_5 t_7 a_18 l_size in
          ~(l_idle_cpu i_5 = 0) ==>
          ~(l_idle_cpu i_6 = 0) ==>
          ~(x = 2) ==>
          ~(int_and 7 x_1 = 0) ==>
          ~(t_7 (swb_shift a_9 i_5) = 0) ==>
          ~(t_7 (swb_shift a_9 i_6) = 0) ==>
          ~(x_3 = 0) ==>
          ~(t_7 (swb_shift a_14 i_5) = 0) ==>
          ~(t_7 (swb_shift a_14 i_6) = 0) ==>
          0 <= i ==>
          i < l_size ==>
          0 <= i_5 ==>
          i_5 < l_size ==>
          0 <= i_6 ==>
          i_6 < l_size ==>
          0 <= i_9 ==>
          i_9 <= l_size ==>
          0 <= x_2 ==>
          x_2 < l_size ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          swb_framed region t_8 ==>
          linked t ==>
          swb_is_uint32 i ==>
          swb_is_uint32 i_1 ==>
          swb_is_sint32 i_2 ==>
          swb_is_sint32 i_3 ==>
          swb_is_sint32 i_4 ==>
          swb_is_sint32 i_7 ==>
          swb_is_sint32 i_8 ==>
          swb_is_sint32 i_9 ==>
          swb_is_sint32 i_10 ==>
          swb_valid_rd t a_1 5 ==>
          swb_is_uint32 x ==>
          swb_is_sint32 x_2 ==>
          swb_valid_rd t a_6 1 ==>
          swb_valid_rd t a_10 1 ==>
          swb_valid_rd t a_2 1 ==>
          swb_valid_rd t a_3 1 ==>
          swb_valid_rd t a_15 1 ==>
          swb_valid_rd t a_7 1 ==>
          swb_valid_rd t (t_8 (swb_shift a_1 2)) 2 ==>
          swb_valid_rd t a_4 2 ==>
          swb_is_sint32 x_1 ==>
          swb_valid_rd t a_16 1 ==>
          swb_valid_rd t a_8 1 ==>
          swb_valid_rd t a_11 1 ==>
          swb_valid_rd t a_12 1 ==>
          swb_valid_rd t a_13 1 ==>
          swb_is_uint8 x_3 ==>
          swb_valid_rd t a_18 l_size ==>
          swb_valid_rd t a_19 l_size ==>
          swb_valid_rw t a_18 l_size ==>
          swb_is_uint8 a_21 ==>
          swb_is_uint8 a_22 ==>
          swb_is_uint8 a_23 ==>
          swb_is_uint8 a_24 ==>
          swb_is_sint32 a_25 ==>
          swb_valid_rd t a_26 l_size ==>
          swb_separated a_18 l_size a_26 l_size ==>
          (if swb_to_uint32 i_8 < l_size then
             i_10 = i_8 /\
             t_4 = t /\
             ~(l_idle_cpu i_10 = 0) /\
             (if a_27 = i_10 then 1 else 0) = i_2 /\
             0 <= i_10 /\
             i_10 < l_size /\
             swb_valid_rd t_4 a_10 1 /\
             swb_valid_rd t_4 a_3 1 /\
             swb_valid_rd t_4 a_5 1 /\
             (~(x_4 = 0) \/
              l_size = i_1 /\
              swb_idle_core
                t_8 (swb_havoc t_6 t_7 a_18 i_1) i_10 /\
              (!i_11 : int.
                let a_29 = swb_shift a i_11 in
                  0 <= i_11 ==>
                  i_11 < i_1 ==>
                  swb_valid_rd t_4 a_29 1 /\
                  swb_valid_rw
                    t_4
                    (swb_shift (t_8 (swb_shift a_29 0)) 0)
                    i_1) /\
              (!a_29 : int # int.
                let a_30 = l_sched_group_cpus a_29 in
                let a_31 = swb_shift (t_8 (swb_shift a_30 0)) 0 in
                  swb_valid_rd t_4 a_30 1 /\
                  swb_valid_rd t_4 a_31 i_1 /\
                  (!i_11 : int.
                    0 <= i_11 ==>
                    i_11 < i_1 ==>
                    swb_separated
                      a_31 i_1
                      (swb_shift
                        (t_8 (swb_shift (swb_shift a i_11) 0)) 0)
                      i_1)) /\
              (!a_29 : int # int.
                let a_30 = l_sched_group_mask a_29 in
                let a_31 = swb_shift (t_8 (swb_shift a_30 0)) 0 in
                  swb_valid_rd t_4 a_30 1 /\
                  swb_valid_rd t_4 a_31 i_1 /\
                  (!i_11 : int.
                    0 <= i_11 ==>
                    i_11 < i_1 ==>
                    swb_separated
                      a_31 i_1
                      (swb_shift
                        (t_8 (swb_shift (swb_shift a i_11) 0)) 0)
                      i_1)) /\
              (!a_29 : int # int.
                let a_30 = l_group_balance_mask a_29 in
                let a_31 = swb_shift (t_8 (swb_shift a_30 0)) 0 in
                  swb_valid_rd t_4 a_30 1 /\
                  swb_valid_rd t_4 a_31 i_1 /\
                  (!i_11 : int.
                    0 <= i_11 ==>
                    i_11 < i_1 ==>
                    swb_separated
                      a_31 i_1
                      (swb_shift
                        (t_8 (swb_shift (swb_shift a i_11) 0)) 0)
                      i_1)) /\
              (!i_11 : int.
                let a_29 = l_cpu_smt_mask i_11 in
                let a_30 = swb_shift (t_8 (swb_shift a_29 0)) 0 in
                  0 <= i_11 ==>
                  i_11 < i_1 ==>
                  swb_valid_rd t_4 a_29 1 /\
                  swb_valid_rd t_4 a_30 i_1 /\
                  (!i_12 : int.
                    0 <= i_12 ==>
                    i_12 < i_1 ==>
                    swb_separated
                      a_30 i_1
                      (swb_shift
                        (t_8 (swb_shift (swb_shift a i_12) 0)) 0)
                      i_1)))
           else
             i_4 = i_3 /\
             t_1 = t /\
             (if i_4 = -1 then
                t_2 = t_1 /\
                l_group_balance_cpu a_12 = i_7 /\
                (if a_27 = i_7 then 1 else 0) = i_2 /\
                swb_valid_rd t_2 a_10 1
              else
                t_3 = t_1 /\
                (if a_27 = i_4 then 1 else 0) = i_2 /\
                swb_valid_rd t_3 a_10 1)) ==>
          (~(x_4 = 0) ==> i_3 = -1) ==>
          (~(i_3 = -1) ==>
            ~(l_idle_cpu i_3 = 0) /\
            ~(a_22 = 0) /\
            ~(a_24 = 0) /\
            0 <= i_3 /\
            i_3 < l_size) ==>
          (i_3 = -1 ==>
            (!i_11 : int.
              ~(a_20 (swb_shift a_14 i_11) = 0) ==>
              0 <= i_11 ==>
              i_11 < l_size ==>
              ~(a_20 (swb_shift a_17 i_11) = 0))) ==>
          ((?i_11 : int.
              ~(a_20 (swb_shift a_17 i_11) = 0) /\
              ~(a_20 (swb_shift a_9 i_11) = 0) /\
              i_11 < l_size /\
              x_5 <= i_11) ==>
            i_8 < l_size) ==>
          ((?i_11 : int.
              ~(a_20 (swb_shift a_17 i_11) = 0) /\
              ~(a_20 (swb_shift a_9 i_11) = 0) /\
              i_11 < l_size /\
              x_5 <= i_11) ==>
            i_8 < l_size /\ x_5 <= i_8) ==>
          ((?i_11 : int.
              ~(a_20 (swb_shift a_17 i_11) = 0) /\
              ~(a_20 (swb_shift a_9 i_11) = 0) /\
              i_11 < l_size /\
              x_5 <= i_11) ==>
            ~(a_21 = 0) /\ ~(a_23 = 0)) ==>
          ((!i_11 : int.
              i_11 < l_size ==>
              x_5 <= i_11 ==>
              a_20 (swb_shift a_17 i_11) = 0 \/
              a_20 (swb_shift a_9 i_11) = 0) ==>
            l_size = i_8) ==>
          (~(i_3 = -1) ==>
            (!i_11 : int.
              ~(a_20 (swb_shift a_9 i_11) = 0) ==>
              ~(a_20 (swb_shift a_14 i_11) = 0) ==>
              0 <= i_11 ==>
              i_11 < i_3 ==>
              i_11 < l_size ==>
              l_idle_cpu i_11 = 0)) ==>
          (i_3 = -1 ==>
            (!i_11 : int.
              ~(a_20 (swb_shift a_9 i_11) = 0) ==>
              ~(a_20 (swb_shift a_14 i_11) = 0) ==>
              0 <= i_11 ==>
              i_11 < i_9 ==>
              i_11 < l_size ==>
              l_idle_cpu i_11 = 0)) ==>
          ((?i_11 : int.
              ~(a_20 (swb_shift a_17 i_11) = 0) /\
              ~(a_20 (swb_shift a_9 i_11) = 0) /\
              i_11 < l_size /\
              x_5 <= i_11) ==>
            (!i_11 : int.
              i_11 < i_8 ==>
              x_5 <= i_11 ==>
              a_20 (swb_shift a_17 i_11) = 0 \/
              a_20 (swb_shift a_9 i_11) = 0)) ==>
          (~(i_3 = -1) ==>
            (!i_11 : int.
              ~(a_20 (swb_shift a_9 i_11) = 0) ==>
              ~(a_20 (swb_shift a_14 i_11) = 0) ==>
              0 <= i_11 ==>
              i_3 <= i_11 ==>
              i_11 < i_9 ==>
              i_11 < l_size ==>
              ~(swb_idle_core t_8 a_20 i_11))) ==>
          (~(i_3 = -1) ==>
            (!i_11 : int.
              ~(a_20 (swb_shift a_14 i_11) = 0) ==>
              0 <= i_11 ==>
              i_11 < l_size ==>
              ~(a_20 (swb_shift a_17 i_11) = 0) \/
              ~(swb_idle_core t_8 a_20 i_11))) ==>
          (!i_11 : int.
            0 <= i_11 ==>
            i_11 < l_size ==>
            swb_separated
              a_19 l_size
              (swb_shift
                (t_8 (swb_shift (swb_shift a i_11) 0)) 0)
              l_size) ==>
          (!i_11 : int.
            let a_29 = swb_shift a i_11 in
              0 <= i_11 ==>
              i_11 < l_size ==>
              swb_valid_rd t a_29 1 /\
              swb_valid_rw
                t
                (swb_shift (t_8 (swb_shift a_29 0)) 0)
                l_size) ==>
          (!i_11 : int.
            0 <= i_11 ==>
            i_11 < l_size ==>
            (~(a_28 (swb_shift a_14 i_11) = 0) <=>
             ~(a_28 (swb_shift a_17 i_11) = 0))) ==>
          (!i_11 : int.
            ~(a_20 (swb_shift a_17 i_11) = 0) ==>
            0 <= i_11 ==>
            i_11 < l_size ==>
            ~(a_20 (swb_shift a_14 i_11) = 0)) ==>
          (!i_11 : int.
            ~(t_7 (swb_shift a_9 i_11) = 0) ==>
            ~(t_7 (swb_shift a_14 i_11) = 0) ==>
            0 <= i_11 ==>
            i_11 < i_6 ==>
            i_11 < l_size ==>
            l_idle_cpu i_11 = 0) ==>
          (!a_29 : int # int.
            let a_30 = l_sched_group_cpus a_29 in
            let a_31 = swb_shift (t_8 (swb_shift a_30 0)) 0 in
              swb_valid_rd t a_30 1 /\
              swb_valid_rd t a_31 l_size /\
              (!i_11 : int.
                0 <= i_11 ==>
                i_11 < l_size ==>
                swb_separated
                  a_31 l_size
                  (swb_shift
                    (t_8 (swb_shift (swb_shift a i_11) 0)) 0)
                  l_size)) ==>
          (!a_29 : int # int.
            let a_30 = l_sched_group_mask a_29 in
            let a_31 = swb_shift (t_8 (swb_shift a_30 0)) 0 in
              swb_valid_rd t a_30 1 /\
              swb_valid_rd t a_31 l_size /\
              (!i_11 : int.
                0 <= i_11 ==>
                i_11 < l_size ==>
                swb_separated
                  a_31 l_size
                  (swb_shift
                    (t_8 (swb_shift (swb_shift a i_11) 0)) 0)
                  l_size)) ==>
          (!a_29 : int # int.
            let a_30 = l_group_balance_mask a_29 in
            let a_31 = swb_shift (t_8 (swb_shift a_30 0)) 0 in
              swb_valid_rd t a_30 1 /\
              swb_valid_rd t a_31 l_size /\
              (!i_11 : int.
                0 <= i_11 ==>
                i_11 < l_size ==>
                swb_separated
                  a_31 l_size
                  (swb_shift
                    (t_8 (swb_shift (swb_shift a i_11) 0)) 0)
                  l_size)) ==>
          (!i_11 : int.
            let a_29 = l_cpu_smt_mask i_11 in
            let a_30 = swb_shift (t_8 (swb_shift a_29 0)) 0 in
              0 <= i_11 ==>
              i_11 < l_size ==>
              swb_valid_rd t a_29 1 /\
              swb_valid_rd t a_30 l_size /\
              (!i_12 : int.
                0 <= i_12 ==>
                i_12 < l_size ==>
                swb_separated
                  a_30 l_size
                  (swb_shift
                    (t_8 (swb_shift (swb_shift a i_12) 0)) 0)
                  l_size)) ==>
          ((x_2 = i_6) <=> ~(i_2 = 0))``;
