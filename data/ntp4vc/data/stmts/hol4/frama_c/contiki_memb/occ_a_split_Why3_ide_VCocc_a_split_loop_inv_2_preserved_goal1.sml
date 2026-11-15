(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/occ_a_split_Why3_ide_VCocc_a_split_loop_inv_2_preserved_goal1:
  preservation of an occurrence-count interval-splitting loop invariant after
  advancing its upper endpoint in a modeled Contiki array. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val occ_a_split_goal1 =
  Parse.Term
    [QUOTE
       ("let mn_shift = " ^
        "\\p : int # int. \\k : int. (FST p, SND p + k) in " ^
        "let mn_is_sint32 = " ^
        "\\z : int. -2147483648 <= z /\\ z < 2147483648 in " ^
        "let mn_occ_axioms = " ^
        "\\l_occ : " ^
        "(((int # int) -> int) -> " ^
        "int -> (int # int) -> int -> int -> int). " ^
        "(!to from mchar e base. " ^
        "to <= from ==> l_occ mchar e base from to = 0) /\\ " ^
        "(!to mchar base e from. " ^
        "mchar (mn_shift base (to - 1)) = e ==> " ^
        "from < to ==> " ^
        "1 + l_occ mchar e base from (to - 1) = " ^
        "l_occ mchar e base from to) /\\ " ^
        "(!to mchar base e from. " ^
        "mchar (mn_shift base (to - 1)) <> e ==> " ^
        "from < to ==> " ^
        "l_occ mchar e base from (to - 1) = " ^
        "l_occ mchar e base from to) in " ^
        "!l_occ : " ^
        "(((int # int) -> int) -> " ^
        "int -> (int # int) -> int -> int -> int). " ^
        "!region : int -> int. " ^
        "!sconst : ((int # int) -> int) -> bool. " ^
        "mn_occ_axioms l_occ ==> " ^
        "!t : (int # int) -> int. " ^
        "!i_3 : int. " ^
        "!a : int # int. " ^
        "!i_2 i_4 i_1 i : int. " ^
        "let x = l_occ t i_3 a i_2 i_4 in " ^
        "let x_1 = 1 + i_1 in " ^
        "x + l_occ t i_3 a i_4 i_1 = " ^
        "l_occ t i_3 a i_2 i_1 ==> " ^
        "i_1 <= i ==> " ^
        "i_4 <= i ==> " ^
        "i_1 < i ==> " ^
        "i_4 <= i_1 ==> " ^
        "i_2 <= i_4 ==> " ^
        "region (FST a) <= 0 ==> " ^
        "i_1 <= 2147483646 ==> " ^
        "sconst t ==> " ^
        "mn_is_sint32 i ==> " ^
        "mn_is_sint32 i_1 ==> " ^
        "mn_is_sint32 i_2 ==> " ^
        "mn_is_sint32 i_3 ==> " ^
        "mn_is_sint32 i_4 ==> " ^
        "mn_is_sint32 x_1 ==> " ^
        "x + l_occ t i_3 a i_4 x_1 = " ^
        "l_occ t i_3 a i_2 x_1")];
