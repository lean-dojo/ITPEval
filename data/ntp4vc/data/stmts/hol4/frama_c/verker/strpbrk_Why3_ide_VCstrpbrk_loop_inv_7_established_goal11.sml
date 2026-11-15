(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_7_established_goal11:
  a strpbrk loop-invariant establishment verification condition concluding
  that the character at a constrained address differs from the current
  non-null character, under the stated memory, address-order, search-result,
  byte-range, valid-string, and intervening-character assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal11 =
  ``let strpbrk_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strpbrk_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strpbrk_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strpbrk_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strpbrk_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?i : int.
          mchar (strpbrk_shift s i) = 0 /\
          strpbrk_is_uint64 i /\
          strpbrk_valid_rw malloc (strpbrk_shift s 0) (1 + i) /\
          (!j : int.
            j <= i ==>
            strpbrk_is_sint8 (mchar (strpbrk_shift s j)))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strpbrk :
        (int # int) -> (int # int) -> (int # int).
        let strpbrk_p_in_array =
          \mchar : (int # int) -> int.
           \s : int # int.
           \c : int.
            ?a : int # int.
              mchar a = c /\
              addr_le s a /\
              addr_lt a
                (strpbrk_shift s (l_strlen mchar s))
        in
          (!p q : int # int.
            FST p = FST q ==>
            (addr_le p q <=> SND p <= SND q)) ==>
          (!p q : int # int.
            FST p = FST q ==>
            (addr_lt p q <=> SND p < SND q)) ==>
          (!z : int.
            strpbrk_is_uint64 (to_uint64 z)) ==>
          (!z : int.
            strpbrk_is_uint64 z ==>
            to_uint64 z = z) ==>
          (!mchar : (int # int) -> int.
           !s : int # int.
            (if mchar (strpbrk_shift s 0) = 0 then
               l_strlen mchar s = 0
             else
               to_uint64
                 (1 + l_strlen mchar (strpbrk_shift s 1)) =
               l_strlen mchar s)) ==>
          (!mchar : (int # int) -> int.
           !s : int # int.
            strpbrk_is_uint64 (l_strlen mchar s)) ==>
          (!mchar : (int # int) -> int.
           !s ct : int # int.
            mchar s = 0 ==>
            l_strpbrk s ct = (0, 0)) ==>
          (!mchar : (int # int) -> int.
           !s ct : int # int.
            mchar s <> 0 ==>
            strpbrk_p_in_array mchar ct (mchar s) ==>
            l_strpbrk s ct = s) ==>
          (!mchar : (int # int) -> int.
           !s ct : int # int.
            mchar s <> 0 ==>
            ~strpbrk_p_in_array mchar ct (mchar s) ==>
            l_strpbrk (strpbrk_shift s 1) ct =
            l_strpbrk s ct) ==>
          !t_1 : (int # int) -> int.
          !a a_2 a_1 : int # int.
          !t : int -> int.
          !a_3 : int # int.
            let x = t_1 a in
              x <> 0 ==>
              l_strpbrk a_2 a_1 = l_strpbrk a a_1 ==>
              region (FST a_1) <= 0 ==>
              region (FST a_2) <= 0 ==>
              linked t ==>
              sconst t_1 ==>
              addr_lt a_3 a_1 ==>
              addr_le a_1 a_3 ==>
              addr_le a_2 a ==>
              strpbrk_is_sint8 x ==>
              strpbrk_p_valid_str t t_1 a ==>
              strpbrk_p_valid_str t t_1 a_1 ==>
              strpbrk_p_valid_str t t_1 a_2 ==>
              addr_le a
                (strpbrk_shift a_2 (l_strlen t_1 a_2)) ==>
              (!a_5 a_4 : int # int.
                addr_lt a_5 a ==>
                addr_le a_1 a_4 ==>
                addr_le a_2 a_5 ==>
                addr_lt a_4
                  (strpbrk_shift a_1 (l_strlen t_1 a_1)) ==>
                t_1 a_5 <> t_1 a_4) ==>
              t_1 a_3 <> x``;
