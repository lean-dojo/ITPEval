(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/match_string_Why3_ide_VCmatch_string_loop_inv_established_goal1:
  a match-string verification condition establishing that the real pointer-array
  length is nonnegative and does not exceed the supplied bound under memory,
  string-validity, and loop-invariant assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal1 =
  ``let ms_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ms_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ms_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ms_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let ms_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let ms_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (ms_shift s n) = 0 /\
          ms_is_uint64 n /\
          ms_valid_rw malloc (ms_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            ms_is_sint8 (mchar (ms_shift s j)))
    in
      !to_uint64 : int -> int.
      !l_real_len :
        ((int # int) -> (int # int)) -> (int # int) -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
        (!z : int. ms_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          ms_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!z : int.
          to_uint64 (to_uint64 z) = to_uint64 z) ==>
        (!mptr : (int # int) -> (int # int).
         !base_addr : int # int.
         !n : int.
          (if n = 0 \/ mptr (ms_shift base_addr 0) = (0, 0) then
             l_real_len mptr base_addr n = 0
           else
             to_uint64
               (1 +
                l_real_len
                  mptr
                  (ms_shift base_addr 1)
                  (to_uint64 (n - 1))) =
             l_real_len mptr base_addr n)) ==>
        (!mptr : (int # int) -> (int # int).
         !base_addr : int # int.
         !n : int.
          ms_is_uint64 (l_real_len mptr base_addr n)) ==>
        !t_2 : (int # int) -> (int # int).
        !a_1 : int # int.
        !i : int.
        !a : int # int.
        !t : int -> int.
        !t_1 : (int # int) -> int.
          let x = l_real_len t_2 a_1 i in
          let a_2 = ms_shift a_1 0 in
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            i <= 2147483647 ==>
            ms_framed region t_2 ==>
            linked t ==>
            sconst t_1 ==>
            ms_is_uint64 i ==>
            ms_p_valid_str t t_1 a ==>
            (x = i ==> ms_valid_rw t a_2 i) ==>
            (x < i ==> ms_valid_rw t a_2 (1 + x)) ==>
            (!i_1 : int.
              0 <= i_1 ==>
              i_1 < x ==>
              ms_is_uint64 i_1 ==>
              ms_p_valid_str
                t t_1 (t_2 (ms_shift a_1 i_1))) ==>
            x <= i /\ 0 <= x``;
