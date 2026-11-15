(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strlen_Why3_ide_VCstrlen_loop_inv_3_preserved_goal6:
  a strlen loop-invariant preservation verification condition concluding the
  updated offset-plus-string-length equality after advancing past a non-null
  signed byte, under the stated memory, address-order, and valid-string
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal6 =
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
        !t_1 : (int # int) -> int.
        !a a_1 : int # int.
        !t : int -> int.
          let x = t_1 a in
          let x_1 = l_strlen t_1 a_1 in
          let x_2 = SND a_1 + x_1 in
          let x_3 = SND a in
            x <> 0 ==>
            x_2 = x_3 + l_strlen t_1 a ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            addr_le a_1 a ==>
            strlen_is_sint8 x ==>
            strlen_p_valid_str t t_1 a ==>
            strlen_p_valid_str t t_1 a_1 ==>
            addr_le a (strlen_shift a_1 x_1) ==>
            1 + x_3 + l_strlen t_1 (strlen_shift a 1) = x_2``;
