(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_chop_Why3_ide_VClist_chop_call_linked_n_before_last_pre_Linked_goal41:
  a linked-list segment can be shortened to end at the node before its last
  node under the stated memory-validity, separation, and uniqueness
  conditions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !i_1 i_2:int.
   !t_1:(int#int)->(int#int).
   !a_1 a:int#int.
   !i:int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let framed =
       \(mptr:(int#int)->(int#int)).
         !p:int#int. region (FST (mptr p)) <= (&0:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_linked_n =
       \(malloc:int->int)
        (mptr:(int#int)->(int#int))
        (bound:int#int) (array:int#int)
        (index:int) (n:int) (last:int#int).
         !P:(int->int)->
            ((int#int)->(int#int))->
            (int#int)->(int#int)->int->int->(int#int)->bool.
           ((!index0:int.
             !malloc0:int->int.
             !mptr0:(int#int)->(int#int).
             !bound0 array0:int#int.
               (&0:int) <= index0
               ==> index0 <= (&2147483646:int)
               ==> P malloc0 mptr0 bound0 array0
                     index0 (&0:int) bound0) /\
            (!index0 n0:int.
             !mptr0:(int#int)->(int#int).
             !array0 root0:int#int.
             !malloc0:int->int.
             !bound0:int#int.
               mptr0 (shift array0 index0) = root0
               ==> (&0:int) < n0
               ==> (&0:int) <= index0
               ==> (&0:int) <= index0 + n0
               ==> index0 + n0 <= (&2147483646:int)
               ==> valid_rw malloc0 root0 (&4:int)
               ==> P malloc0 mptr0
                     (mptr0 (shift root0 (&0:int)))
                     array0 ((&1:int) + index0)
                     (n0 - (&1:int)) bound0
               ==> P malloc0 mptr0 root0 array0
                     index0 n0 bound0))
           ==> P malloc mptr bound array index n last in
     let x = i_1 + i_2 in
     let a_2 = t_1 (shift a_1 x) in
     let a_3 = t_1 (shift a_2 (&0:int)) in
     let a_4 = t_1 (shift a_3 (&0:int)) in
     let a_5 = t_1 a in
     let a_6 = shift a_1 (&0:int) in
     let x_1 = i + i_1 in
     a_4 = ((&0:int),(&0:int))
     ==> ~(a_4 = a_5)
     ==> ~(a_4 = t_1 (shift a_5 (&0:int)))
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> (&2:int) + i_2 <= i
     ==> framed t_1
     ==> linked t
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> valid_rw t a (&1:int)
     ==> valid_rw t a_6 (&2147483646:int)
     ==> separated a (&1:int) a_6 (&2147483646:int)
     ==> separated a_5 (&4:int) a_6 (&2147483646:int)
     ==> valid_rw t a_3 (&4:int)
     ==> p_linked_n t t_1 a_5 a_1 i_1 i a_4
     ==> p_linked_n t t_1 a_2 a_1 x (i - i_2) a_4
     ==> (!i_3:int.
            i_1 <= i_3
            ==> i_3 < x_1
            ==> separated a (&1:int)
                  (t_1 (shift a_1 i_3)) (&4:int))
     ==> (!i_3:int.
            i_1 <= i_3
            ==> i_3 < x_1
            ==> separated (t_1 (shift a_1 i_3))
                  (&4:int) a_6 (&2147483646:int))
     ==> (!i_4 i_3:int.
            ~(i_4 = i_3)
            ==> i_1 <= i_3
            ==> i_1 <= i_4
            ==> i_3 < x_1
            ==> i_4 < x_1
            ==> ~(t_1 (shift a_1 i_4) =
                  t_1 (shift a_1 i_3)))
     ==> (!i_4 i_3:int.
            ~(i_4 = i_3)
            ==> i_1 <= i_3
            ==> i_1 <= i_4
            ==> i_3 < x_1
            ==> i_4 < x_1
            ==> separated (t_1 (shift a_1 i_4))
                  (&4:int) (t_1 (shift a_1 i_3)) (&4:int))
     ==> p_linked_n t t_1 a_5 a_1 i_1
           (i - (&1:int))
           (t_1 (shift a_1 (i + i_1 - (&1:int))))`;;
