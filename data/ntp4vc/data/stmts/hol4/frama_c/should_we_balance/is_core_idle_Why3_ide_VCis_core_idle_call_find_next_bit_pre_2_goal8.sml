(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_call_find_next_bit_pre_2_goal8:
  validity of the CPU SMT-mask read required before a find-next-bit call,
  under modeled address, allocation, framing, separation, and integer-bound
  conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal8 =
  ``let ici_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ici_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ici_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ici_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let ici_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ici_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ici_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let ici_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !i_2 : int.
      !t_2 : (int # int) -> (int # int).
      !i i_1 : int.
      !a : int # int.
      !t : int -> int.
      !t_1 : (int # int) -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !l_size : int.
      !l_idle_cpu : int -> int.
      !l_sched_group_cpus : (int # int) -> (int # int).
      !l_sched_group_mask : (int # int) -> (int # int).
      !l_group_balance_mask : (int # int) -> (int # int).
      !l_cpu_smt_mask : int -> (int # int).
        let ici_mask_member =
          \mint : (int # int) -> int.
           \mptr : (int # int) -> (int # int).
           \cpu : int. \member : int.
            ~(mint
                (ici_shift
                  (mptr (ici_shift (l_cpu_smt_mask cpu) 0))
                  member) = 0)
        in
        0 < l_size /\ l_size <= 2147483647 ==>
        (!cpu : int. ici_is_uint8 (l_idle_cpu cpu)) ==>
        (!i : int.
         !mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
           0 <= i ==>
           i < l_size ==>
           ici_mask_member mint mptr i i) ==>
        (!mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
         !j i : int.
           ici_mask_member mint mptr j i ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           ici_mask_member mint mptr i j) ==>
        (!mptr : (int # int) -> (int # int).
         !i : int.
         !mint : (int # int) -> int.
         !j k : int.
           ici_mask_member mint mptr i j ==>
           ici_mask_member mint mptr j k ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           0 <= k ==>
           k < l_size ==>
           ici_mask_member mint mptr i k) ==>
        let a_1 = ici_shift (l_cpu_smt_mask i_2) 0 in
        let a_2 = t_2 a_1 in
          ~(l_idle_cpu i_2 = 0) ==>
          0 <= i ==>
          i < l_size ==>
          0 <= i_1 ==>
          0 <= i_2 ==>
          i_2 < l_size ==>
          i_1 <= l_size ==>
          region (FST a) <= 0 ==>
          ici_framed region t_2 ==>
          linked t ==>
          ici_is_uint32 i ==>
          ici_is_sint32 i_1 ==>
          ici_is_sint32 i_2 ==>
          ici_valid_rd t a_1 1 ==>
          (!i_3 : int.
            ~(t_1 (ici_shift a_2 i_3) = 0) ==>
            0 <= i_3 ==>
            i_3 < i_1 ==>
            ~(l_idle_cpu i_3 = 0)) ==>
          (!i_3 : int.
            let a_3 = ici_shift a i_3 in
              0 <= i_3 ==>
              i_3 < l_size ==>
              ici_valid_rd t a_3 1 /\
              ici_valid_rw
                t
                (ici_shift (t_2 (ici_shift a_3 0)) 0)
                l_size) ==>
          (!a_3 : int # int.
            let a_4 = l_sched_group_cpus a_3 in
            let a_5 = ici_shift (t_2 (ici_shift a_4 0)) 0 in
              ici_valid_rd t a_4 1 /\
              ici_valid_rd t a_5 l_size /\
              (!i_3 : int.
                0 <= i_3 ==>
                i_3 < l_size ==>
                ici_separated
                  a_5 l_size
                  (ici_shift
                    (t_2 (ici_shift (ici_shift a i_3) 0)) 0)
                  l_size)) ==>
          (!a_3 : int # int.
            let a_4 = l_sched_group_mask a_3 in
            let a_5 = ici_shift (t_2 (ici_shift a_4 0)) 0 in
              ici_valid_rd t a_4 1 /\
              ici_valid_rd t a_5 l_size /\
              (!i_3 : int.
                0 <= i_3 ==>
                i_3 < l_size ==>
                ici_separated
                  a_5 l_size
                  (ici_shift
                    (t_2 (ici_shift (ici_shift a i_3) 0)) 0)
                  l_size)) ==>
          (!a_3 : int # int.
            let a_4 = l_group_balance_mask a_3 in
            let a_5 = ici_shift (t_2 (ici_shift a_4 0)) 0 in
              ici_valid_rd t a_4 1 /\
              ici_valid_rd t a_5 l_size /\
              (!i_3 : int.
                0 <= i_3 ==>
                i_3 < l_size ==>
                ici_separated
                  a_5 l_size
                  (ici_shift
                    (t_2 (ici_shift (ici_shift a i_3) 0)) 0)
                  l_size)) ==>
          (!i_3 : int.
            let a_3 = l_cpu_smt_mask i_3 in
            let a_4 = ici_shift (t_2 (ici_shift a_3 0)) 0 in
              0 <= i_3 ==>
              i_3 < l_size ==>
              ici_valid_rd t a_3 1 /\
              ici_valid_rd t a_4 l_size /\
              (!i_4 : int.
                0 <= i_4 ==>
                i_4 < l_size ==>
                ici_separated
                  a_4 l_size
                  (ici_shift
                    (t_2 (ici_shift (ici_shift a i_4) 0)) 0)
                  l_size)) ==>
          ici_valid_rd t (ici_shift a_2 0) l_size``;
