(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/index_of_unexisting_item_Why3_ide_VCindex_of_unexisting_item_post_goal0:
  an index-of search returns its upper bound when the target pointer is absent
  throughout the search interval, under the stated memory, framing, and
  signed-integer conditions. This file contains no proof.
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
     ==> !i i_1:int.
         !a a_1:int#int.
         !t:(int#int)->(int#int).
           (&0:int) <= i
           ==> (&0:int) <= i_1
           ==> region (FST a) <= (&0:int)
           ==> region (FST a_1) <= (&0:int)
           ==> framed t
           ==> is_sint32 i
           ==> is_sint32 i_1
           ==> (!i_2:int.
                  i_2 < i
                  ==> i_1 <= i_2
                  ==> ~(t (shift a_1 i_2) = a))
           ==> l_index_of t a a_1 i_1 i = i`;;
