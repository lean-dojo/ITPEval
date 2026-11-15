(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_not_exists_post_2_goal13:
  a strchrnul nonexistence-postcondition verification condition concluding
  that it is false that every position before the modeled string length
  differs from the current non-null signed byte, under the stated memory,
  address-order, valid-string, search-result, and no-earlier-match
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal13 =
  ``let scn_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let scn_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let scn_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let scn_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let scn_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let scn_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (scn_shift s n) = 0 /\
          scn_is_uint64 n /\
          scn_valid_rw malloc (scn_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            scn_is_sint8 (mchar (scn_shift s j)))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_sint8 to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strchrnul :
        ((int # int) -> int) ->
        (int # int) -> int -> (int # int).
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        (!z : int.
          scn_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          scn_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int.
          scn_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          scn_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (scn_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (scn_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          scn_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !str : int # int.
         !c : int.
          (if mchar str = c then
             l_strchrnul mchar str c = str
           else if mchar str = 0 then
             l_strchrnul mchar str c = str
           else
             l_strchrnul mchar (scn_shift str 1) c =
             l_strchrnul mchar str c)) ==>
        !t_1 : (int # int) -> int.
        !a a_1 : int # int.
        !i : int.
        !t : int -> int.
          let x = t_1 a in
          let x_1 = l_strlen t_1 a_1 in
            ~(x = 0) ==>
            x = to_sint8 i ==>
            l_strchrnul t_1 a_1 x =
              l_strchrnul t_1 a x ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            scn_is_sint32 i ==>
            addr_le a_1 a ==>
            scn_is_sint8 x ==>
            scn_p_valid_str t t_1 a ==>
            scn_p_valid_str t t_1 a_1 ==>
            addr_le a (scn_shift a_1 x_1) ==>
            (!a_2 : int # int.
              addr_lt a_2 a ==>
              addr_le a_1 a_2 ==>
              ~(x = t_1 a_2)) ==>
            ~(!i_1 : int.
              0 <= i_1 ==>
              i_1 < x_1 ==>
              ~(t_1 (scn_shift a_1 i_1) = x))``;
