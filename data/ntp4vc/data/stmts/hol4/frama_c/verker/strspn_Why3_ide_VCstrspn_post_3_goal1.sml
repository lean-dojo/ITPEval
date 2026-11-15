(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strspn_Why3_ide_VCstrspn_post_3_goal1:
  a strspn postcondition verification condition concluding that the byte at
  a constrained source-string address occurs within the accept-string range,
  under the stated memory, address-order, string-length, span-length,
  byte-range, valid-string, branch, and earlier-character assumptions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal1 =
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
          !a_1 a a_2 a_3 a_5 a_4 : int # int.
          !t_1 : (int # int) -> int.
          !t : int -> int.
          !i i_1 i_2 : int.
            let x = SND a_1 in
            let x_1 = SND a in
            let x_2 = l_strlen t_1 a in
            let x_3 = t_1 a_1 in
            let x_4 = t_1 a_2 in
            let a_6 =
              strspn_shift a_3 (l_strlen t_1 a_3)
            in
              x + l_strspn a_1 a_3 =
              x_1 + l_strspn a a_3 ==>
              x_1 <= x ==>
              region (FST a) <= 0 ==>
              region (FST a_3) <= 0 ==>
              x <= x_1 + x_2 ==>
              linked t ==>
              sconst t_1 ==>
              strspn_is_uint64 i ==>
              addr_le a a_1 ==>
              addr_le a a_5 ==>
              strspn_is_sint8 x_3 ==>
              strspn_is_sint8 x_4 ==>
              strspn_p_valid_str t t_1 a ==>
              strspn_p_valid_str t t_1 a_1 ==>
              strspn_p_valid_str t t_1 a_3 ==>
              addr_lt a_5 (strspn_shift a i) ==>
              strspn_is_uint64 (x - x_1) ==>
              addr_le a_1 (strspn_shift a x_2) ==>
              (if x_3 = 0 then
                 i_1 = i /\
                 i_1 + x_1 = x
               else
                 a_2 = a_1 /\
                 i_2 = i /\
                 t_1 a_4 = 0 /\
                 i_2 + x_1 = SND a_2 /\
                 addr_le a_3 a_4 /\
                 strspn_p_valid_str t t_1 a_4 /\
                 ~strspn_p_in_array t_1 a_3 x_4 /\
                 addr_le a_4 a_6 /\
                 (!a_7 : int # int.
                   addr_lt a_7 a_4 ==>
                   addr_le a_3 a_7 ==>
                   x_4 <> t_1 a_7)) ==>
              (!a_7 : int # int.
                addr_lt a_7 a_1 ==>
                addr_le a a_7 ==>
                ?a_8 : int # int.
                  t_1 a_7 = t_1 a_8 /\
                  addr_le a_3 a_8 /\
                  addr_lt a_8 a_6) ==>
              ?a_7 : int # int.
                t_1 a_5 = t_1 a_7 /\
                addr_le a_3 a_7 /\
                addr_lt a_7 a_6``;
