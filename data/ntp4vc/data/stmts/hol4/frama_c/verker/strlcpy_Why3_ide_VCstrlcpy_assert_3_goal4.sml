(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strlcpy_Why3_ide_VCstrlcpy_assert_3_goal4:
  a strlcpy verification condition asserting that the updated destination
  string has the copied length after bounded copying and null termination.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal4 =
  ``let sl_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sl_separated =
      \p : int # int. \n : int.
       \q : int # int. \m : int.
        n <= 0 \/
        m <= 0 \/
        ~(FST p = FST q) \/
        SND q + m <= SND p \/
        SND p + n <= SND q
    in
    let sl_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let sl_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        ~(0 = FST p) /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let sl_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let sl_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let sl_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (sl_shift s n) = 0 /\
          sl_is_uint64 n /\
          sl_valid_rw malloc (sl_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            sl_is_sint8 (mchar (sl_shift s j)))
    in
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !havoc :
        ((int # int) -> int) ->
        ((int # int) -> int) ->
        (int # int) -> int -> (int # int) -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
        (!z : int.
          sl_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          sl_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!z : int.
          to_uint64 (to_uint64 z) = to_uint64 z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sl_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (sl_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sl_is_uint64 (l_strlen mchar s)) ==>
        (!m0 m1 : (int # int) -> int.
         !p : int # int.
         !n : int.
         !q : int # int.
          havoc m0 m1 p n q =
          (if sl_separated q 1 p n then m1 q else m0 q)) ==>
        !a_1 a : int # int.
        !t_2 t_1 : (int # int) -> int.
        !i_1 i : int.
        !t : int -> int.
          let x = FST a_1 in
          let x_1 = FST a in
          let x_2 = l_strlen t_2 a in
          let a_2 = sl_shift a_1 0 in
          let a_3 = havoc t_1 t_2 a_2 i_1 in
          let a_4 =
            \q : int # int.
              if q = sl_shift a_1 i_1 then 0 else a_3 q
          in
            i <> 0 ==>
            x <> x_1 ==>
            t_2 (sl_shift a x_2) = 0 ==>
            region x_1 <= 0 ==>
            region x <= 0 ==>
            linked t ==>
            sconst t_2 ==>
            sl_is_uint64 i ==>
            sl_is_uint64 i_1 ==>
            sl_p_valid_str t t_2 a ==>
            sl_is_uint64 x_2 ==>
            sl_valid_rd t (sl_shift a 0) i_1 ==>
            sl_valid_rw t a_2 i ==>
            sl_valid_rw t a_2 i_1 ==>
            sl_p_valid_str t a_4 a_1 ==>
            (if i <= x_2 then
               to_uint64 (i - 1) = i_1
             else
               x_2 = i_1) ==>
            (!i_2 : int.
              0 <= i_2 ==>
              i_2 < x_2 ==>
              t_2 (sl_shift a i_2) <> 0) ==>
            (!i_2 : int.
              0 <= i_2 ==>
              i_2 < i_1 ==>
              a_3 (sl_shift a_1 i_2) =
              a_3 (sl_shift a i_2)) ==>
            l_strlen a_4 a_1 = i_1``;
