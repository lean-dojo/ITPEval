(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strcmp_Why3_ide_VCstrcmp_loop_inv_3_preserved_goal5:
  a strcmp loop-invariant preservation verification condition concluding that
  the one-byte successor of the current first-string address lies between the
  comparison string's base and terminating address, under the stated memory,
  string-validity, comparison, byte-range, address, and prefix-equality
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal5 =
  ``let strcmp_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strcmp_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strcmp_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let strcmp_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strcmp_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strcmp_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (strcmp_shift s n) = 0 /\
          strcmp_is_uint64 n /\
          strcmp_valid_rw malloc (strcmp_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            strcmp_is_sint8 (mchar (strcmp_shift s j)))
    in
    let strcmp_l_cmp =
      \u v : int.
        if v = u then 0 else if u < v then -1 else 1
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint8 to_sint8 to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strncmp :
        ((int # int) -> int) ->
        (int # int) -> (int # int) -> int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          strcmp_is_uint8 (to_uint8 z)) ==>
        (!z : int.
          strcmp_is_uint8 z ==>
          to_uint8 z = z) ==>
        (!z : int.
          strcmp_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          strcmp_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int.
          to_sint8 (to_uint8 z) = to_sint8 z) ==>
        (!z : int.
          strcmp_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          strcmp_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (strcmp_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (strcmp_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          strcmp_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !cs ct : int # int.
         !n : int.
          (if n = -1 then
             l_strncmp mchar cs ct n = 0
           else if
             mchar (strcmp_shift ct 0) =
             mchar (strcmp_shift cs 0)
           then
             l_strncmp
               mchar
               (strcmp_shift cs 1)
               (strcmp_shift ct 1)
               (n - 1) =
             l_strncmp mchar cs ct n
           else
             strcmp_l_cmp
               (to_uint8 (mchar (strcmp_shift cs 0)))
               (to_uint8 (mchar (strcmp_shift ct 0))) =
             l_strncmp mchar cs ct n)) ==>
        !t_1 : (int # int) -> int.
        !a a_2 a_3 a_1 : int # int.
        !t : int -> int.
          let x = t_1 a in
          let x_1 = to_uint8 x in
          let x_2 = t_1 a_2 in
          let x_3 = SND a_2 in
          let x_4 = SND a_3 in
          let x_5 = l_strlen t_1 a_3 in
          let x_6 = x_3 - x_4 in
          let x_7 = t_1 (strcmp_shift a_3 x_6) in
          let x_8 = t_1 (strcmp_shift a_1 x_6) in
          let a_4 = strcmp_shift a_1 (l_strlen t_1 a_1) in
          let a_5 = strcmp_shift a 1 in
            ~(x_1 = 0) ==>
            to_uint8 x_2 = x_1 ==>
            l_strncmp t_1 a_3 a_1 (l_strlen t_1 a_3) =
              l_strncmp t_1 a_2 a (l_strlen t_1 a_2) ==>
            SND a_1 + x_3 = SND a + x_4 ==>
            x_4 + x_5 = x_3 + l_strlen t_1 a_2 ==>
            x_7 = x_8 ==>
            ((!i : int.
               0 <= i ==>
               i <= x_5 ==>
               to_uint8 (t_1 (strcmp_shift a_3 i)) =
               to_uint8 (t_1 (strcmp_shift a_1 i))) <=>
             (!i : int.
               0 <= i ==>
               i <= x_5 ==>
               t_1 (strcmp_shift a_3 i) =
               t_1 (strcmp_shift a_1 i))) ==>
            region (FST a_1) <= 0 ==>
            region (FST a_3) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            addr_le a_1 a ==>
            addr_le a_3 a_2 ==>
            strcmp_is_sint8 x ==>
            strcmp_is_sint8 x_2 ==>
            strcmp_p_valid_str t t_1 a ==>
            strcmp_p_valid_str t t_1 a_1 ==>
            strcmp_p_valid_str t t_1 a_2 ==>
            strcmp_p_valid_str t t_1 a_3 ==>
            addr_le a a_4 ==>
            addr_le a_2 (strcmp_shift a_3 x_5) ==>
            strcmp_is_sint8 x_8 ==>
            strcmp_is_sint8 x_7 ==>
            (!i : int.
              0 <= i ==>
              i + x_4 < x_3 ==>
              t_1 (strcmp_shift a_3 i) =
              t_1 (strcmp_shift a_1 i)) ==>
            addr_le a_1 a_5 /\ addr_le a_5 a_4``;
