(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/index_of_not_in_subrange_Why3_ide_VCindex_of_not_in_subrange_loop_inv_3_preserved_goal4:
  preservation of an index-of loop invariant when the current array entry is
  not the searched pointer, under the memory, framing, range, and signed-
  integer conditions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !l_index_of:
      ((int#int)->(int#int))->
      (int#int)->(int#int)->int->int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let framed =
       \(mptr:(int#int)->(int#int)).
         !p:int#int. region (FST (mptr p)) <= (&0:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     ((!up down:int.
       !mptr:(int#int)->(int#int).
       !item array:int#int.
         up <= down
         ==> (&0:int) <= up
         ==> l_index_of mptr item array down up = up) /\
      (!mptr:(int#int)->(int#int).
       !array:int#int.
       !down:int.
       !item:int#int.
       !up:int.
         mptr (shift array down) = item
         ==> (&0:int) <= down
         ==> down < up
         ==> l_index_of mptr item array down up = down) /\
      (!mptr:(int#int)->(int#int).
       !array:int#int.
       !down:int.
       !item:int#int.
       !up:int.
         ~(mptr (shift array down) = item)
         ==> (&0:int) <= down
         ==> down < up
         ==> l_index_of mptr item array ((&1:int) + down) up =
             l_index_of mptr item array down up))
     ==> !i_2:int.
         !t:(int#int)->(int#int).
         !a a_1:int#int.
         !i_4 i i_1 i_3:int.
           let x = (&1:int) + i_2 in
           let x_1 = l_index_of t a a_1 i_4 i in
           ~(t (shift a_1 i_2) = a)
           ==> (&0:int) <= i
           ==> i_2 <= i_1
           ==> i_4 <= i_1
           ==> i_2 < i_1
           ==> i_3 <= i_2
           ==> i_4 <= i_2
           ==> i_4 <= i_3
           ==> (&0:int) <= i_4
           ==> region (FST a) <= (&0:int)
           ==> region (FST a_1) <= (&0:int)
           ==> framed t
           ==> is_sint32 i
           ==> is_sint32 i_1
           ==> is_sint32 i_2
           ==> is_sint32 i_3
           ==> is_sint32 i_4
           ==> is_sint32 x
           ==> (!i_5:int.
                  i_5 < i_1
                  ==> i_4 <= i_5
                  ==> ~(t (shift a_1 i_5) = a))
           ==> (!i_5:int.
                  i_5 < i_2
                  ==> i_4 <= i_5
                  ==> x_1 = l_index_of t a a_1 i_2 i)
           ==> l_index_of t a a_1 x i = x_1`;;
