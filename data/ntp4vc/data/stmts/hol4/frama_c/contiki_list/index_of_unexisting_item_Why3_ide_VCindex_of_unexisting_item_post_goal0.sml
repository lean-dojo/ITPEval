(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/index_of_unexisting_item_Why3_ide_VCindex_of_unexisting_item_post_goal0:
  a modeled list-index search returns its upper endpoint when the sought
  address does not occur in the searched interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val index_of_unexisting_item_Why3_ide_VCindex_of_unexisting_item_post_goal0 =
  ``let iou_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let iou_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let iou_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !i i_1 : int.
      !a a_1 : int # int.
      !t : (int # int) -> (int # int).
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
           mptr (iou_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (iou_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        0 <= i ==>
        0 <= i_1 ==>
        region (FST a) <= 0 ==>
        region (FST a_1) <= 0 ==>
        iou_framed region t ==>
        iou_is_sint32 i ==>
        iou_is_sint32 i_1 ==>
        (!i_2 : int.
          i_2 < i ==>
          i_1 <= i_2 ==>
          ~(t (iou_shift a_1 i_2) = a)) ==>
        l_index_of t a a_1 i_1 i = i``;
