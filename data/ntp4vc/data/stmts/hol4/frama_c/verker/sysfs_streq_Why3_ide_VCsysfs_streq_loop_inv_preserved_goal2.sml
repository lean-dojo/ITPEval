(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_preserved_goal2:
  a sysfs string-equality loop-invariant preservation verification condition
  concluding that the incremented common-prefix offset is unchanged by
  unsigned-64 conversion, under the stated current-byte, string-length,
  memory, byte-range, valid-string, and prefix-equality assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
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
      !l_strlen :
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
        !a_1 : int # int.
        !i : int.
        !t_1 : (int # int) -> int.
        !a : int # int.
        !t : int -> int.
          let a_2 = sysfs_shift a_1 i in
          let x = t_1 a_2 in
          let a_3 = sysfs_shift a i in
          let x_1 = t_1 a_3 in
          let x_2 = 1 + i in
            ~(x = 0) ==>
            x = x_1 ==>
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
            sysfs_is_sint8 x_1 ==>
            sysfs_is_sint8 x ==>
            sysfs_p_valid_str t t_1 a_3 ==>
            sysfs_p_valid_str t t_1 a_2 ==>
            (!i_1 : int.
              0 <= i_1 ==>
              i_1 < i ==>
              t_1 (sysfs_shift a_1 i_1) =
              t_1 (sysfs_shift a i_1)) ==>
            x_2 = to_uint64 x_2``;
