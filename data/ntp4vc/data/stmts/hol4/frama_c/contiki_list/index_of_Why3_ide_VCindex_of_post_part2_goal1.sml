(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/index_of_Why3_ide_VCindex_of_post_part2_goal1:
  correctness of the first matching index returned by the modeled list
  index search. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val index_of_Why3_ide_VCindex_of_post_part2_goal1 =
  ``let io_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let io_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let io_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let io_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !t_1 : (int # int) -> (int # int).
      !a : int # int.
      !i_1 i i_2 : int.
      !t : int -> int.
        (!up down : int.
         !mptr : (int # int) -> (int # int).
         !item array : int # int.
           up <= down ==>
           0 <= up ==>
           l_index_of mptr item array down up = up) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           mptr (io_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (io_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let a_1 = t_1 (io_shift a i_1) in
          0 <= i ==>
          i_1 <= i ==>
          i_1 < i ==>
          i_2 <= i_1 ==>
          0 <= i_2 ==>
          i_2 < i ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          io_framed region t_1 ==>
          linked t ==>
          io_is_sint32 i ==>
          io_is_sint32 i_1 ==>
          io_is_sint32 i_2 ==>
          (i_2 <= i ==>
           io_valid_rw t (io_shift a i_2) (i - i_2)) ==>
          (!i_3 : int.
            i_3 < i_1 ==>
            i_2 <= i_3 ==>
            ~(a_1 = t_1 (io_shift a i_3))) ==>
          l_index_of t_1 a_1 a i_2 i = i_1``;
