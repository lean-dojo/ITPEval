(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strim_Why3_ide_VCstrim_len_assign_normal_part7_goal21:
  a string-trimming length-assignment verification condition concluding that
  the one-byte region after the current address is included in the original
  string region, under the stated memory, address-order, byte-range,
  valid-string, non-whitespace, and intervening-whitespace assumptions. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal21 =
  ``let strim_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strim_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strim_invalid =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        malloc (FST p) <= SND p \/ SND p + n <= 0
    in
    let strim_included =
      \p : int # int. \a : int. \q : int # int. \b : int.
        0 < a ==>
        0 <= b /\
        FST p = FST q /\
        SND q <= SND p /\
        SND p + a <= SND q + b
    in
    let strim_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strim_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strim_p_isspace =
      \z : int.
        z = 9 \/ z = 10 \/ z = 12 \/ z = 13 \/ z = 32
    in
    let strim_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (strim_shift s n) = 0 /\
          strim_is_uint64 n /\
          strim_valid_rw malloc (strim_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            strim_is_sint8 (mchar (strim_shift s j)))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        (!z : int.
          strim_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          strim_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (strim_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (strim_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          strim_is_uint64 (l_strlen mchar s)) ==>
        !t_1 : (int # int) -> int.
        !a : int # int.
        !p : bool.
        !a_1 : int # int.
        !t : int -> int.
          let x = l_strlen t_1 a in
          let a_2 = strim_shift a (x - 1) in
          let x_1 = t_1 a_2 in
          let x_2 = t_1 a_1 in
          let a_3 = strim_shift a (-1) in
          let a_4 = strim_shift a_1 1 in
            ~(x = 0) ==>
            t_1 (strim_shift a x) = 0 ==>
            ~(x_1 = 0) ==>
            0 < x ==>
            region (FST a) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            strim_is_sint8 x_2 ==>
            strim_p_valid_str t t_1 a ==>
            strim_is_uint64 x ==>
            addr_le a_3 a_1 ==>
            ~strim_invalid t a_4 1 ==>
            addr_le a_1 a_2 ==>
            strim_is_sint8 x_1 ==>
            (if addr_le a a_1 then
               p = F /\ ~strim_p_isspace x_2
             else
               a_3 = a_1 \/ ~strim_p_isspace x_2) ==>
            (!i : int.
              0 <= i ==>
              i < x ==>
              ~(t_1 (strim_shift a i) = 0)) ==>
            (!a_5 : int # int.
              addr_lt a_1 a_5 ==>
              addr_le a_5 a_2 ==>
              strim_p_isspace (t_1 a_5)) ==>
            strim_included a_4 1 (strim_shift a 0) (1 + x)``;
