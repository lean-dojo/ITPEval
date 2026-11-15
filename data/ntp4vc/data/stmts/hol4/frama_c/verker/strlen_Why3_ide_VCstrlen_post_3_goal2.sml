(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strlen_Why3_ide_VCstrlen_post_3_goal2:
  a strlen postcondition verification condition concluding that every
  nonnegative offset strictly before the converted distance to the current
  null byte is itself non-null, under the stated offset-length relation,
  memory, address-order, byte-range, and valid-string assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
  ``let strlen_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strlen_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strlen_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strlen_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strlen_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (strlen_shift s n) = 0 /\
          strlen_is_uint64 n /\
          strlen_valid_rw malloc (strlen_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            strlen_is_sint8 (mchar (strlen_shift s j)))
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          strlen_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          strlen_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (strlen_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (strlen_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          strlen_is_uint64 (l_strlen mchar s)) ==>
        !a_1 : int # int.
        !t_1 : (int # int) -> int.
        !a : int # int.
        !i : int.
        !t : int -> int.
          let x = SND a_1 in
          let x_1 = l_strlen t_1 a_1 in
          let x_2 = SND a in
          let x_3 = to_uint64 (x_2 - x) in
            t_1 a = 0 ==>
            x + x_1 = x_2 + l_strlen t_1 a ==>
            0 <= i ==>
            region (FST a_1) <= 0 ==>
            i < x_3 ==>
            linked t ==>
            sconst t_1 ==>
            addr_le a_1 a ==>
            strlen_p_valid_str t t_1 a ==>
            strlen_p_valid_str t t_1 a_1 ==>
            addr_le a (strlen_shift a_1 x_1) ==>
            strlen_is_sint8
              (t_1 (strlen_shift a_1 x_3)) ==>
            ~(t_1 (strlen_shift a_1 i) = 0)``;
