(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strreplace_Why3_ide_VCstrreplace_loop_inv_preserved_goal4:
  a strreplace loop-invariant preservation verification condition concluding
  that the updated memory contains a valid C string after the current byte,
  under the stated memory, address-order, byte-range, string-validity, havoc,
  update, and prefix-replacement assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal4 =
  ``let sr_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sr_separated =
      \p : int # int. \n : int.
       \q : int # int. \m : int.
        n <= 0 \/
        m <= 0 \/
        ~(FST p = FST q) \/
        SND q + m <= SND p \/
        SND p + n <= SND q
    in
    let sr_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let sr_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let sr_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let sr_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (sr_shift s n) = 0 /\
          sr_is_uint64 n /\
          sr_valid_rw malloc (sr_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            sr_is_sint8 (mchar (sr_shift s j)))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !havoc :
        ((int # int) -> int) ->
        ((int # int) -> int) ->
        (int # int) -> int -> (int # int) -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        (!z : int.
          sr_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          sr_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sr_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (sr_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sr_is_uint64 (l_strlen mchar s)) ==>
        (!m0 m1 : (int # int) -> int.
         !p : int # int.
         !n : int.
         !q : int # int.
          havoc m0 m1 p n q =
          (if sr_separated q 1 p n then m1 q else m0 q)) ==>
        !t_2 : (int # int) -> int.
        !a_1 : int # int.
        !t_1 : (int # int) -> int.
        !a : int # int.
        !t : int -> int.
        !i i_1 : int.
        !t_3 : (int # int) -> int.
          let x = l_strlen t_2 a_1 in
          let a_2 = sr_shift a_1 x in
          let a_3 = havoc t_1 t_2 (sr_shift a_1 0) x in
          let a_4 = a_3 a in
            t_2 a_2 = 0 ==>
            ~(a_4 = 0) ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            sconst t_2 ==>
            sr_is_sint8 i ==>
            sr_is_sint8 i_1 ==>
            addr_le a_1 a ==>
            sr_p_valid_str t t_2 a_1 ==>
            sr_is_uint64 x ==>
            addr_le a a_2 ==>
            sr_is_sint8 a_4 ==>
            sr_p_valid_str t a_3 a ==>
            sr_p_valid_str t a_3 a_1 ==>
            (if a_4 = i then
               (\q : int # int.
                  if q = a then i_1 else a_3 q) = t_3
             else
               a_3 = t_3) ==>
            (!i_2 : int.
              0 <= i_2 ==>
              i_2 < x ==>
              ~(t_2 (sr_shift a_1 i_2) = 0)) ==>
            (!a_5 : int # int.
              addr_le a a_5 ==>
              addr_lt a_5 a_2 ==>
              a_3 a_5 = t_2 a_5) ==>
            (!a_5 : int # int.
              t_2 a_5 = i ==>
              addr_lt a_5 a ==>
              addr_le a_1 a_5 ==>
              a_3 a_5 = i_1) ==>
            (!a_5 : int # int.
              let x_1 = t_2 a_5 in
                ~(x_1 = i) ==>
                addr_lt a_5 a ==>
                addr_le a_1 a_5 ==>
                a_3 a_5 = x_1) ==>
            sr_p_valid_str t t_3 (sr_shift a 1)``;
