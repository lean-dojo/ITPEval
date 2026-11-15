(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_nonempty_dst1_post_goal16:
  a CPU-mask and-not postcondition equating source-mask bit tests with the
  corresponding nonzero entry in the havoced destination memory. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal16 =
  ``let cn_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let cn_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let cn_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let cn_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let cn_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if cn_separated q 1 p n then m1 q else m0 q
    in
    let cn_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let cn_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let cn_is_sint32 =
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
        let cn_mask_member =
          \mint : (int # int) -> int.
           \mptr : (int # int) -> (int # int).
           \cpu : int. \member : int.
            ~(mint
                (cn_shift
                  (mptr (cn_shift (l_cpu_smt_mask cpu) 0))
                  member) = 0)
        in
        0 < l_size /\ l_size <= 2147483647 ==>
        (!cpu : int. cn_is_uint8 (l_idle_cpu cpu)) ==>
        (!i : int.
         !mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
           0 <= i ==>
           i < l_size ==>
           cn_mask_member mint mptr i i) ==>
        (!mint : (int # int) -> int.
         !mptr : (int # int) -> (int # int).
         !j i : int.
           cn_mask_member mint mptr j i ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           cn_mask_member mint mptr i j) ==>
        (!mptr : (int # int) -> (int # int).
         !i : int.
         !mint : (int # int) -> int.
         !j k : int.
           cn_mask_member mint mptr i j ==>
           cn_mask_member mint mptr j k ==>
           0 <= i ==>
           i < l_size ==>
           0 <= j ==>
           j < l_size ==>
           0 <= k ==>
           k < l_size ==>
           cn_mask_member mint mptr i k) ==>
        (!z : int.
          0 <= z /\ z < 4294967296 ==>
          to_uint32 z = z) ==>
        let a_3 = t_3 (cn_shift a 0) in
        let a_4 = cn_shift a_3 0 in
        let a_5 = t_3 (cn_shift a_1 0) in
        let a_6 = cn_shift a_5 0 in
        let a_7 = t_3 (cn_shift a_2 0) in
        let a_8 = cn_shift a_7 0 in
        let a_9 = cn_havoc t_1 t_2 a_8 l_size in
          ~((0, 0) = a_2) ==>
          to_uint32 i = l_size ==>
          0 <= i ==>
          0 <= i_1 ==>
          i_1 < l_size ==>
          i <= l_size ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          cn_framed region t_3 ==>
          linked t ==>
          cn_is_sint32 i ==>
          cn_valid_rd t a 1 ==>
          cn_valid_rd t a_1 1 ==>
          cn_valid_rd t a_2 1 ==>
          cn_valid_rd t a_4 l_size ==>
          cn_valid_rd t a_6 l_size ==>
          cn_valid_rw t a_8 l_size ==>
          (a_2 <> a ==>
            cn_separated a_8 l_size a_4 l_size) ==>
          (a_2 <> a_1 ==>
            cn_separated a_8 l_size a_6 l_size) ==>
          (!i_2 : int.
            0 <= i_2 ==>
            i_2 < l_size ==>
            cn_separated
              a_8 l_size
              (cn_shift
                (t_3 (cn_shift (l_cpu_smt_mask i_2) 0)) 0)
              l_size) ==>
          (!i_2 : int.
            let a_10 = cn_shift a_7 i_2 in
              i <= i_2 ==>
              i_2 < l_size ==>
              (~(a_9 a_10 = 0) <=> ~(t_2 a_10 = 0))) ==>
          (!i_2 : int.
            0 <= i_2 ==>
            i_2 < i ==>
            (t_2 (cn_shift a_3 i_2) = 0 /\
             ~(t_2 (cn_shift a_5 i_2) = 0) <=>
             ~(a_9 (cn_shift a_7 i_2) = 0))) ==>
          (t_2 (cn_shift a_3 i_1) = 0 /\
           ~(t_2 (cn_shift a_5 i_1) = 0) <=>
           ~(a_9 (cn_shift a_7 i_1) = 0))``;
