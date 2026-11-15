(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/index_of_Why3_ide_VCindex_of_post_part3_goal2:
  an index-of search returns the upper search bound when the target pointer
  does not occur from the lower bound up to that bound, under the stated
  memory, framing, linkage, and signed-integer conditions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_index_of:
      ((int#int)->(int#int))->
      (int#int)->(int#int)->int->int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
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
     ==> !i i_1 i_2:int.
         !a a_1:int#int.
         !t_1:(int#int)->(int#int).
         !t:int->int.
           (&0:int) <= i
           ==> i_1 <= i
           ==> i <= i_1
           ==> i_2 <= i_1
           ==> (&0:int) <= i_2
           ==> i_2 < i
           ==> region (FST a) <= (&0:int)
           ==> region (FST a_1) <= (&0:int)
           ==> framed t_1
           ==> linked t
           ==> is_sint32 i
           ==> is_sint32 i_1
           ==> is_sint32 i_2
           ==> (i_2 <= i
                ==> valid_rw t (shift a_1 i_2) (i - i_2))
           ==> (!i_3:int.
                  i_3 < i_1
                  ==> i_2 <= i_3
                  ==> ~(t_1 (shift a_1 i_3) = a))
           ==> l_index_of t_1 a a_1 i_2 i_1 = i_1`;;
