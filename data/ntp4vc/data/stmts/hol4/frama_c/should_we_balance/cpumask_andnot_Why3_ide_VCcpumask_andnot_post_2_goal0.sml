(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_post_2_goal0:
  preservation of the idle-core condition after a CPU-mask and-not operation,
  using modeled address arithmetic, memory validity, separation, and havoc.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let cp_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let cp_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let cp_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let cp_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let cp_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if cp_separated q 1 p n then m1 q else m0 q
    in
    let cp_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let cp_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let cp_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !t_3 : (int # int) -> (int # int).
      !a a_1 a_2 : int # int.
      !t_1 t_2 : (int # int) -> int.
      !i i_1 : int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
      !l_size : int.
      !l_idle_cpu : int -> int.
      !l_cpu_smt_mask : int -> (int # int).
        let cp_mask_member =
          \mint : (int # int) -> int.
           \mptr : (int # int) -> (int # int).
           \cpu : int. \member : int.
            ~(mint
                (cp_shift
                  (mptr (cp_shift (l_cpu_smt_mask cpu) 0))
                  member) = 0)
        in
        0 < l_size /\ l_size <= 2147483647 ==>
        (!cpu : int. cp_is_uint8 (l_idle_cpu cpu)) ==>
        (!i : int.
         !mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
           0 <= i ==>
           i < l_size ==>
           cp_mask_member mint mptr i i) ==>
        (!mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
         !j i : int.
           cp_mask_member mint mptr j i ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           cp_mask_member mint mptr i j) ==>
        (!mptr : (int # int) -> (int # int).
         !i : int.
         !mint : (int # int) -> int.
         !j k : int.
           cp_mask_member mint mptr i j ==>
           cp_mask_member mint mptr j k ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           0 <= k ==>
           k < l_size ==>
           cp_mask_member mint mptr i k) ==>
        (!z : int.
          0 <= z /\ z < 4294967296 ==>
          to_uint32 z = z) ==>
        let cp_idle_core =
          \mptr : (int # int) -> (int # int).
           \mint : (int # int) -> int.
           \cpu : int.
            !j : int.
              ~(mint
                  (cp_shift
                    (mptr (cp_shift (l_cpu_smt_mask cpu) 0)) j) = 0) ==>
              0 <= j ==>
              j < l_size ==>
              ~(l_idle_cpu j = 0)
        in
        let a_3 = t_3 (cp_shift a 0) in
        let a_4 = cp_shift a_3 0 in
        let a_5 = t_3 (cp_shift a_1 0) in
        let a_6 = cp_shift a_5 0 in
        let a_7 = t_3 (cp_shift a_2 0) in
        let a_8 = cp_shift a_7 0 in
        let a_9 = cp_havoc t_1 t_2 a_8 l_size in
          ~((0, 0) = a_2) ==>
          to_uint32 i = l_size ==>
          0 <= i ==>
          0 <= i_1 ==>
          i_1 < l_size ==>
          i <= l_size ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          cp_framed region t_3 ==>
          linked t ==>
          cp_is_sint32 i ==>
          cp_valid_rd t a 1 ==>
          cp_valid_rd t a_1 1 ==>
          cp_valid_rd t a_2 1 ==>
          cp_valid_rd t a_4 l_size ==>
          cp_valid_rd t a_6 l_size ==>
          cp_valid_rw t a_8 l_size ==>
          cp_idle_core t_3 a_9 i_1 ==>
          (a_2 <> a ==>
            cp_separated a_8 l_size a_4 l_size) ==>
          (a_2 <> a_1 ==>
            cp_separated a_8 l_size a_6 l_size) ==>
          (!i_2 : int.
            0 <= i_2 ==>
            i_2 < l_size ==>
            cp_separated
              a_8 l_size
              (cp_shift
                (t_3 (cp_shift (l_cpu_smt_mask i_2) 0)) 0)
              l_size) ==>
          (!i_2 : int.
            let a_10 = cp_shift a_7 i_2 in
              i <= i_2 ==>
              i_2 < l_size ==>
              (~(a_9 a_10 = 0) <=> ~(t_2 a_10 = 0))) ==>
          (!i_2 : int.
            0 <= i_2 ==>
            i_2 < i ==>
            (t_2 (cp_shift a_3 i_2) = 0 /\
             ~(t_2 (cp_shift a_5 i_2) = 0) <=>
             ~(a_9 (cp_shift a_7 i_2) = 0))) ==>
          cp_idle_core t_3 t_2 i_1``;
