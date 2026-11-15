(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_assert_8_goal16:
  a sysfs string-equality verification condition concluding that the sysfs
  length of the first string is the common-prefix offset, under the stated
  newline and null terminators, prefix equality, memory validity, byte-range,
  and string-length assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal16 =
  ``let sysfs_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sysfs_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let sysfs_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let sysfs_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let sysfs_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let sysfs_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (sysfs_shift s n) = 0 /\
          sysfs_is_uint64 n /\
          sysfs_valid_rw malloc (sysfs_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            sysfs_is_sint8 (mchar (sysfs_shift s j)))
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 to_sint32 : int -> int.
      !l_strlen l_sysfs_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strncmp :
        ((int # int) -> int) ->
        (int # int) -> (int # int) -> int -> int.
        (!z : int.
          sysfs_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          sysfs_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!z : int.
          sysfs_is_sint32 (to_sint32 z)) ==>
        (!z : int.
          sysfs_is_sint32 z ==>
          to_sint32 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sysfs_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (sysfs_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sysfs_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sysfs_shift s 0) = 0 \/
              mchar (sysfs_shift s 0) = 10 /\
              mchar (sysfs_shift s 1) = 0
           then
             l_sysfs_strlen mchar s = 0
           else
             to_uint64
               (1 + l_sysfs_strlen mchar (sysfs_shift s 1)) =
             l_sysfs_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sysfs_is_uint64 (l_sysfs_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s1 s2 : int # int.
         !n : int.
          (if n = 0 then
             l_strncmp mchar s1 s2 n = 0
           else if mchar (sysfs_shift s2 0) =
                   mchar (sysfs_shift s1 0)
           then
             if mchar (sysfs_shift s1 0) = 0 then
               l_strncmp mchar s1 s2 n = 0
             else
               l_strncmp mchar
                 (sysfs_shift s1 1)
                 (sysfs_shift s2 1)
                 (to_uint64 (n - 1)) =
               l_strncmp mchar s1 s2 n
           else
             to_sint32
               (mchar (sysfs_shift s1 0) -
                mchar (sysfs_shift s2 0)) =
             l_strncmp mchar s1 s2 n)) ==>
        (!mchar : (int # int) -> int.
         !s1 s2 : int # int.
         !n : int.
          sysfs_is_sint32 (l_strncmp mchar s1 s2 n)) ==>
        !a : int # int.
        !i : int.
        !a_1 : int # int.
        !t_1 : (int # int) -> int.
        !t : int -> int.
          let a_2 = sysfs_shift a i in
          let a_3 = sysfs_shift a_1 i in
          let x = l_sysfs_strlen t_1 a_2 in
            t_1 a_2 = 10 ==>
            t_1 a_3 = 0 ==>
            l_sysfs_strlen t_1 a_3 = x ==>
            t_1 (sysfs_shift a (1 + i)) = 0 ==>
            i <= l_strlen t_1 a ==>
            i <= l_strlen t_1 a_1 ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            sysfs_is_uint64 i ==>
            sysfs_p_valid_str t t_1 a ==>
            sysfs_p_valid_str t t_1 a_1 ==>
            l_strncmp t_1 a_1 a i = 0 ==>
            sysfs_p_valid_str t t_1 a_2 ==>
            sysfs_p_valid_str t t_1 a_3 ==>
            l_strncmp t_1 a_3 a_2 x = 0 ==>
            (!i_1 : int.
              0 <= i_1 ==>
              i_1 < i ==>
              t_1 (sysfs_shift a_1 i_1) =
              t_1 (sysfs_shift a i_1)) ==>
            (!i_1 : int.
              let x_1 = t_1 (sysfs_shift a i_1) in
              let x_2 = t_1 (sysfs_shift a_1 i_1) in
                0 <= i_1 ==>
                i_1 < i ==>
                sysfs_is_uint64 i_1 ==>
                ~(x_1 = 0) /\
                ~(x_2 = 0) /\
                x_2 = x_1) ==>
            l_sysfs_strlen t_1 a = i``;
