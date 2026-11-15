(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_7_preserved_goal10:
  a strpbrk loop-invariant preservation verification condition concluding
  that the character at a constrained address differs from the current
  character of the second string, under the stated memory, address-order,
  search-result, membership, byte-range, valid-string, and
  intervening-character assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal10 =
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
          !a a_1 a_2 a_3 : int # int.
          !t : int -> int.
          !a_4 : int # int.
            let x = t_1 a in
            let x_1 = t_1 a_1 in
            let a_5 =
              strpbrk_shift a_2 (l_strlen t_1 a_2)
            in
              x <> 0 ==>
              x_1 <> 0 ==>
              x_1 <> x ==>
              l_strpbrk a_3 a_2 = l_strpbrk a_1 a_2 ==>
              region (FST a_2) <= 0 ==>
              region (FST a_3) <= 0 ==>
              linked t ==>
              sconst t_1 ==>
              addr_le a_2 a ==>
              addr_le a_2 a_4 ==>
              addr_le a_3 a_1 ==>
              strpbrk_is_sint8 x ==>
              strpbrk_is_sint8 x_1 ==>
              strpbrk_p_valid_str t t_1 a ==>
              strpbrk_p_valid_str t t_1 a_1 ==>
              strpbrk_p_valid_str t t_1 a_2 ==>
              strpbrk_p_valid_str t t_1 a_3 ==>
              addr_lt a_4 (strpbrk_shift a 1) ==>
              addr_le a a_5 ==>
              addr_le a_1
                (strpbrk_shift a_3 (l_strlen t_1 a_3)) ==>
              (strpbrk_p_in_array t_1 a_2 x_1 ==>
               strpbrk_p_in_array t_1 a x_1) ==>
              (!a_6 : int # int.
                addr_lt a_6 a ==>
                addr_le a_2 a_6 ==>
                x_1 <> t_1 a_6) ==>
              (!a_7 a_6 : int # int.
                addr_lt a_7 a_1 ==>
                addr_le a_2 a_6 ==>
                addr_le a_3 a_7 ==>
                addr_lt a_6 a_5 ==>
                t_1 a_7 <> t_1 a_6) ==>
              t_1 a_4 <> x_1``;
