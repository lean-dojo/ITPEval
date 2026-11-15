(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/index_of_not_in_subrange_Why3_ide_VCindex_of_not_in_subrange_loop_inv_3_preserved_goal4:
  preservation of the modeled list-index loop invariant when the current
  array entry is not the sought address. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val index_of_not_in_subrange_Why3_ide_VCindex_of_not_in_subrange_loop_inv_3_preserved_goal4 =
  ``let ios_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ios_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ios_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !i_2 : int.
      !t : (int # int) -> (int # int).
      !a a_1 : int # int.
      !i_4 i i_1 i_3 : int.
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
           mptr (ios_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (ios_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let x = 1 + i_2 in
        let x_1 = l_index_of t a a_1 i_4 i in
          ~(t (ios_shift a_1 i_2) = a) ==>
          0 <= i ==>
          i_2 <= i_1 ==>
          i_4 <= i_1 ==>
          i_2 < i_1 ==>
          i_3 <= i_2 ==>
          i_4 <= i_2 ==>
          i_4 <= i_3 ==>
          0 <= i_4 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          ios_framed region t ==>
          ios_is_sint32 i ==>
          ios_is_sint32 i_1 ==>
          ios_is_sint32 i_2 ==>
          ios_is_sint32 i_3 ==>
          ios_is_sint32 i_4 ==>
          ios_is_sint32 x ==>
          (!i_5 : int.
            i_5 < i_1 ==>
            i_4 <= i_5 ==>
            ~(t (ios_shift a_1 i_5) = a)) ==>
          (!i_5 : int.
            i_5 < i_2 ==>
            i_4 <= i_5 ==>
            x_1 = l_index_of t a a_1 i_2 i) ==>
          l_index_of t a a_1 x i = x_1``;
