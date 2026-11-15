(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_assert_rte_signed_overflow_goal9:
  signed 32-bit upper-bound overflow safety for incrementing the count of free
  allocation markers in a modeled Contiki memb structure. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal9 =
  Parse.Term
    [QUOTE
       ("let mn_shift = " ^
        "\\p : int # int. \\k : int. (FST p, SND p + k) in " ^
        "let mn_valid_rw = " ^
        "\\malloc : int -> int. \\p : int # int. \\n : int. " ^
        "0 < n ==> " ^
        "0 < FST p /\\ 0 <= SND p /\\ " ^
        "SND p + n <= malloc (FST p) in " ^
        "let mn_valid_rd = " ^
        "\\malloc : int -> int. \\p : int # int. \\n : int. " ^
        "0 < n ==> " ^
        "FST p <> 0 /\\ 0 <= SND p /\\ " ^
        "SND p + n <= malloc (FST p) in " ^
        "let mn_separated = " ^
        "\\p : int # int. \\n : int. " ^
        "\\q : int # int. \\m : int. " ^
        "n <= 0 \\/ m <= 0 \\/ FST p <> FST q \\/ " ^
        "SND q + m <= SND p \\/ SND p + n <= SND q in " ^
        "let mn_framed = " ^
        "\\region : int -> int. " ^
        "\\mptr : (int # int) -> (int # int). " ^
        "!p : int # int. region (FST (mptr p)) <= 0 in " ^
        "let mn_is_sint32 = " ^
        "\\z : int. -2147483648 <= z /\\ z < 2147483648 in " ^
        "let mn_is_uint16 = " ^
        "\\z : int. 0 <= z /\\ z < 65536 in " ^
        "let mn_p_valid_memb = " ^
        "\\malloc : int -> int. " ^
        "\\mptr : (int # int) -> (int # int). " ^
        "\\mint : (int # int) -> int. " ^
        "\\memb : int # int. " ^
        "let size = mint (mn_shift memb 0) in " ^
        "let count = mint (mn_shift memb 1) in " ^
        "let total = count * size in " ^
        "let used = mptr (mn_shift memb 2) in " ^
        "let mem = mptr (mn_shift memb 3) in " ^
        "let used_start = mn_shift used 0 in " ^
        "let mem_start = mn_shift mem 0 in " ^
        "0 < size /\\ total <= 2147483647 /\\ " ^
        "mn_valid_rw malloc memb 4 /\\ " ^
        "mn_valid_rw malloc used 1 /\\ " ^
        "mn_valid_rw malloc mem 1 /\\ " ^
        "mn_valid_rw malloc used_start count /\\ " ^
        "mn_valid_rw malloc mem_start total /\\ " ^
        "mn_separated used_start count mem_start total in " ^
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
        "!linked : (int -> int) -> bool. " ^
        "!sconst : ((int # int) -> int) -> bool. " ^
        "mn_occ_axioms l_occ ==> " ^
        "!a : int # int. " ^
        "!t_3 : (int # int) -> (int # int). " ^
        "!i : int. " ^
        "!t_1 t_2 : (int # int) -> int. " ^
        "!t : int -> int. " ^
        "let a_1 = mn_shift a 2 in " ^
        "let a_2 = t_3 a_1 in " ^
        "let a_3 = mn_shift a_2 i in " ^
        "let a_4 = mn_shift a 1 in " ^
        "let x = t_1 a_4 in " ^
        "let x_1 = l_occ t_2 0 a_2 0 i in " ^
        "t_2 a_3 = 0 ==> " ^
        "0 <= i ==> i < x ==> i <= x ==> " ^
        "region (FST a) <= 0 ==> x_1 <= i ==> " ^
        "mn_framed region t_3 ==> linked t ==> sconst t_2 ==> " ^
        "mn_is_sint32 i ==> mn_is_uint16 x ==> " ^
        "mn_p_valid_memb t t_3 t_1 a ==> " ^
        "mn_valid_rd t a_1 1 ==> mn_valid_rd t a_4 1 ==> " ^
        "mn_valid_rd t a_3 1 ==> mn_is_sint32 x_1 ==> " ^
        "x_1 <= 2147483646")];
