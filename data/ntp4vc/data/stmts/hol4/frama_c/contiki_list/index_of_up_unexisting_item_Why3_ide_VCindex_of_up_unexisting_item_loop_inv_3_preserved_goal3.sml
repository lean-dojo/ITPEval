(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_3_preserved_goal3:
  preservation of the modeled upward list-index loop invariant after
  incrementing the current search index. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_3_preserved_goal3 =
  ``let iouu_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let iouu_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let iouu_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !i_1 : int.
      !t : (int # int) -> (int # int).
      !a a_1 : int # int.
      !i_3 i i_2 : int.
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
           mptr (iouu_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (iouu_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let x = 1 + i_1 in
          l_index_of t a a_1 i_3 i = i ==>
          i_1 <= i ==>
          i_3 <= i ==>
          i_1 < i ==>
          i_2 <= i_1 ==>
          i_3 <= i_1 ==>
          i_3 <= i_2 ==>
          0 <= i_3 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          iouu_framed region t ==>
          iouu_is_sint32 i ==>
          iouu_is_sint32 i_1 ==>
          iouu_is_sint32 i_2 ==>
          iouu_is_sint32 i_3 ==>
          iouu_is_sint32 x ==>
          (!i_4 : int.
            i_4 < i_1 ==>
            i_3 <= i_4 ==>
            ~(t (iouu_shift a_1 i_4) = a)) ==>
          (!i_4 : int.
            i_4 < i_1 ==>
            i_3 <= i_4 ==>
            l_index_of t a a_1 i_1 i = i) ==>
          l_index_of t a a_1 x i = i``;
