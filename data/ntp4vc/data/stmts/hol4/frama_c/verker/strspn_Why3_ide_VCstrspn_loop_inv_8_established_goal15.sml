(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strspn_Why3_ide_VCstrspn_loop_inv_8_established_goal15:
  a strspn eighth loop-invariant establishment verification condition
  concluding that the byte at a constrained address differs from the current
  non-null byte, under the stated memory, address-order, string-length,
  span-length, byte-range, valid-string, and intervening-character
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal15 =
  ``let strspn_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strspn_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strspn_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strspn_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strspn_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?i : int.
          mchar (strspn_shift s i) = 0 /\
          strspn_is_uint64 i /\
          strspn_valid_rw malloc (strspn_shift s 0) (1 + i) /\
          (!j : int.
            j <= i ==>
            strspn_is_sint8 (mchar (strspn_shift s j)))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strspn :
        (int # int) -> (int # int) -> int.
        let strspn_p_in_array =
          \mchar : (int # int) -> int.
           \s : int # int.
           \c : int.
            ?a : int # int.
              mchar a = c /\
              addr_le s a /\
              addr_lt a
                (strspn_shift s (l_strlen mchar s))
        in
          (!p q : int # int.
            FST p = FST q ==>
            (addr_le p q <=> SND p <= SND q)) ==>
          (!p q : int # int.
            FST p = FST q ==>
            (addr_lt p q <=> SND p < SND q)) ==>
          (!z : int.
            strspn_is_uint64 (to_uint64 z)) ==>
          (!z : int.
            strspn_is_uint64 z ==>
            to_uint64 z = z) ==>
          (!mchar : (int # int) -> int.
           !s : int # int.
            (if mchar (strspn_shift s 0) = 0 then
               l_strlen mchar s = 0
             else
               to_uint64
                 (1 + l_strlen mchar (strspn_shift s 1)) =
               l_strlen mchar s)) ==>
          (!mchar : (int # int) -> int.
           !s : int # int.
            strspn_is_uint64 (l_strlen mchar s)) ==>
          (!mchar : (int # int) -> int.
           !s accept : int # int.
            mchar s = 0 ==>
            l_strspn s accept = 0) ==>
          (!mchar : (int # int) -> int.
           !s accept : int # int.
            mchar s <> 0 ==>
            ~strspn_p_in_array mchar accept (mchar s) ==>
            l_strspn s accept = 0) ==>
          (!mchar : (int # int) -> int.
           !s accept : int # int.
            mchar s <> 0 ==>
            strspn_p_in_array mchar accept (mchar s) ==>
            1 + l_strspn (strspn_shift s 1) accept =
            l_strspn s accept) ==>
          !t_1 : (int # int) -> int.
          !a_1 a a_3 : int # int.
          !t : int -> int.
          !a_2 : int # int.
            let x = t_1 a_1 in
            let x_1 = SND a_1 in
            let x_2 = SND a in
            let x_3 = l_strlen t_1 a in
              x <> 0 ==>
              x_1 + l_strspn a_1 a_3 =
              x_2 + l_strspn a a_3 ==>
              x_2 <= x_1 ==>
              region (FST a) <= 0 ==>
              region (FST a_3) <= 0 ==>
              x_1 <= x_2 + x_3 ==>
              linked t ==>
              sconst t_1 ==>
              addr_lt a_2 a_3 ==>
              addr_le a a_1 ==>
              addr_le a_3 a_2 ==>
              strspn_is_sint8 x ==>
              strspn_p_valid_str t t_1 a ==>
              strspn_p_valid_str t t_1 a_1 ==>
              strspn_p_valid_str t t_1 a_3 ==>
              strspn_is_uint64 (x_1 - x_2) ==>
              addr_le a_1 (strspn_shift a x_3) ==>
              (!a_4 : int # int.
                addr_lt a_4 a_1 ==>
                addr_le a a_4 ==>
                ?a_5 : int # int.
                  t_1 a_4 = t_1 a_5 /\
                  addr_le a_3 a_5 /\
                  addr_lt a_5
                    (strspn_shift a_3 (l_strlen t_1 a_3))) ==>
              t_1 a_2 <> x``;
