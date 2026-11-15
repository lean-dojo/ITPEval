(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strchr_Why3_ide_VCstrchr_exists_post_3_goal12:
  a strchr existence-postcondition verification condition concluding that a
  later candidate address does not contain the searched character, under the
  stated address-order, valid-string, search-result, branch, and no-earlier-
  match assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal12 =
  ``let sc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let sc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let sc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let sc_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let sc_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (sc_shift s n) = 0 /\
          sc_is_uint64 n /\
          sc_valid_rw malloc (sc_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            sc_is_sint8 (mchar (sc_shift s j)))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_sint8 to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strchr :
        ((int # int) -> int) ->
        (int # int) -> int -> (int # int).
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        (!z : int.
          sc_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          sc_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int.
          sc_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          sc_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sc_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (sc_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sc_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !str : int # int.
         !c : int.
          (if mchar str = c then
             l_strchr mchar str c = str
           else if mchar str = 0 then
             l_strchr mchar str c = (0, 0)
           else
             l_strchr mchar (sc_shift str 1) c =
             l_strchr mchar str c)) ==>
        !t_1 : (int # int) -> int.
        !a_3 a a_1 a_2 : int # int.
        !i : int.
        !t : int -> int.
        !a_4 : int # int.
          let x = t_1 a_3 in
          let x_1 = t_1 a in
          let x_2 = t_1 a_1 in
          let a_5 = sc_shift a_2 (l_strlen t_1 a_2) in
            x = to_sint8 i ==>
            l_strchr t_1 a_2 x = l_strchr t_1 a x ==>
            region (FST a_2) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            sc_is_sint32 i ==>
            addr_lt a_4 a_1 ==>
            addr_le a_2 a ==>
            addr_le a_2 a_3 ==>
            addr_le a_2 a_4 ==>
            sc_is_sint8 x_1 ==>
            sc_is_sint8 x_2 ==>
            sc_p_valid_str t t_1 a ==>
            sc_p_valid_str t t_1 a_2 ==>
            addr_le a a_5 ==>
            addr_le a_3 a_5 ==>
            (if x = x_1 then
               a_1 = a /\
               (a_5 = a_1 <=> x_2 = 0) /\
               (addr_lt a_1 a_5 <=> ~(x_2 = 0))
             else
               (0, 0) = a_1 /\ x_1 = 0) ==>
            (!a_6 : int # int.
              addr_lt a_6 a ==>
              addr_le a_2 a_6 ==>
              ~(x = t_1 a_6)) ==>
            ~(t_1 a_4 = x)``;
