(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memmem_Why3_ide_VCmemmem_disjoint_occr_not_occur_err_part1_goal1:
  a memmem disjoint-occurrence/non-occurrence verification condition giving
  length-order cases or an existential shift that aligns memory reads, under
  unsigned bounds, memory-validity, separation, linking, and region
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal1 =
  ``let mc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mc_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let mc_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_2 a_3 : int # int.
      !i i_1 : int.
      !t : int -> int.
      !t_1 : (int # int) -> int.
      !a_1 a : int # int.
        let a_4 = mc_shift a_2 0 in
        let a_5 = mc_shift a_3 0 in
          0 <= i ==>
          0 <= i_1 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          linked t ==>
          mc_is_uint32 i ==>
          mc_is_uint32 i_1 ==>
          mc_valid_rw t a_4 i_1 ==>
          mc_valid_rw t a_5 i ==>
          mc_separated a_5 i a_4 i_1 ==>
          i = 0 \/
          i_1 = 0 \/
          i < i_1 \/
          (i <> 0 /\ i_1 <> 0 /\ i_1 <= i) \/
          (?i_2 : int.
            0 <= i_2 /\
            i_2 + i_1 <= i /\
            (!i_3 : int.
              t_1 (mc_shift a_1 (i_3 + i_2)) =
                t_1 (mc_shift a i_3) \/
              i_3 < 0 \/
              i_1 <= i_3))``;
