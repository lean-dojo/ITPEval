(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_assert_rte_signed_overflow_goal14:
  signed 32-bit upper-bound overflow safety for incrementing a CPU-mask loop
  index under modeled memory validity, separation, framing, and value
  conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal14 =
  ``let ca_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ca_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ca_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ca_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let ca_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if ca_separated q 1 p n then m1 q else m0 q
    in
    let ca_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ca_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let ca_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !a_1 a_2 a : int # int.
      !t_3 : (int # int) -> (int # int).
      !i : int.
      !t_1 t_2 : (int # int) -> int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
      !l_size : int.
      !l_idle_cpu : int -> int.
      !l_cpu_smt_mask : int -> (int # int).
        let ca_mask_member =
          \mint : (int # int) -> int.
           \mptr : (int # int) -> (int # int).
           \cpu : int. \member : int.
            ~(mint
                (ca_shift
                  (mptr (ca_shift (l_cpu_smt_mask cpu) 0))
                  member) = 0)
        in
        0 < l_size /\ l_size <= 2147483647 ==>
        (!cpu : int. ca_is_uint8 (l_idle_cpu cpu)) ==>
        (!i : int.
         !mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
           0 <= i ==>
           i < l_size ==>
           ca_mask_member mint mptr i i) ==>
        (!mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
         !j i : int.
           ca_mask_member mint mptr j i ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           ca_mask_member mint mptr i j) ==>
        (!mptr : (int # int) -> (int # int).
         !i : int.
         !mint : (int # int) -> int.
         !j k : int.
           ca_mask_member mint mptr i j ==>
           ca_mask_member mint mptr j k ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           0 <= k ==>
           k < l_size ==>
           ca_mask_member mint mptr i k) ==>
        (!z : int.
          0 <= z /\ z < 4294967296 ==>
          to_uint32 z = z) ==>
        let a_3 = ca_shift a_1 0 in
        let a_4 = ca_shift a_2 0 in
        let a_5 = ca_shift a 0 in
        let a_6 = t_3 a_5 in
        let a_7 = ca_shift a_6 0 in
        let a_8 = t_3 a_3 in
        let a_9 = ca_shift a_8 0 in
        let a_10 = ca_shift a_8 i in
        let a_11 = t_3 a_4 in
        let a_12 = ca_shift a_11 0 in
        let a_13 = ca_havoc t_1 t_2 a_12 l_size in
        let a_14 = ca_shift a_6 i in
        let a_15 = a_13 a_14 in
        let a_16 = a_13 a_10 in
          ~((0, 0) = a_2) ==>
          ~(to_uint32 i = l_size) ==>
          0 <= i ==>
          i <= l_size ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          ca_framed region t_3 ==>
          linked t ==>
          ca_is_sint32 i ==>
          ca_valid_rd t a 1 ==>
          ca_valid_rd t a_1 1 ==>
          ca_valid_rd t a_2 1 ==>
          ca_valid_rd t a_3 1 ==>
          ca_valid_rd t a_4 1 ==>
          ca_valid_rd t a_7 l_size ==>
          ca_valid_rd t a_9 l_size ==>
          ca_valid_rd t a_10 1 ==>
          ca_valid_rw t a_12 l_size ==>
          ca_valid_rw t (ca_shift a_11 i) 1 ==>
          ca_is_uint8 a_15 ==>
          ca_is_uint8 a_16 ==>
          (a_2 <> a ==>
            ca_separated a_12 l_size a_7 l_size) ==>
          (a_2 <> a_1 ==>
            ca_separated a_12 l_size a_9 l_size) ==>
          (a_16 = 0 \/ a_16 = 1) ==>
          (a_16 = 0 \/
            ca_valid_rd t a_5 1 /\
            ca_valid_rd t a_14 1 /\
            (a_15 = 0 \/ a_15 = 1)) ==>
          (!i_1 : int.
            0 <= i_1 ==>
            i_1 < l_size ==>
            ca_separated
              a_12 l_size
              (ca_shift
                (t_3 (ca_shift (l_cpu_smt_mask i_1) 0)) 0)
              l_size) ==>
          (!i_1 : int.
            let a_17 = ca_shift a_11 i_1 in
              i <= i_1 ==>
              i_1 < l_size ==>
              (~(a_13 a_17 = 0) <=> ~(t_2 a_17 = 0))) ==>
          (!i_1 : int.
            0 <= i_1 ==>
            i_1 < i ==>
            (t_2 (ca_shift a_6 i_1) = 0 /\
             ~(t_2 (ca_shift a_8 i_1) = 0) <=>
             ~(a_13 (ca_shift a_11 i_1) = 0))) ==>
          i <= 2147483646``;
