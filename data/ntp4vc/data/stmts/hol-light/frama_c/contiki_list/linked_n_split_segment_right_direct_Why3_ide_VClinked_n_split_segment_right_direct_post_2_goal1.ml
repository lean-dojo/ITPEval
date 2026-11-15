(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_split_segment_right_direct_Why3_ide_VClinked_n_split_segment_right_direct_post_2_goal1:
  direct extraction of the final one-node segment from the right side of a
  linked-list segment. This file contains no proof.
*)

let statement =
  `!t_1:(int#int)->(int#int).
   !a_2:int#int.
   !i i_1:int.
   !a a_1:int#int.
   !t:int->int.
   !region:int->int.
   !linked:(int->int)->bool.
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
     let a_3 =
       t_1
         (shift
           (t_1 (shift a_2 (i + i_1 - (&1:int))))
           (&0:int)) in
     (&0:int) < i
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_2) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> framed t_1
     ==> linked t
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> valid_rw t (shift a_2 (&0:int)) (&2147483646:int)
     ==> p_linked_n t t_1 a a_2 i_1 ((&1:int) + i) a_1
     ==> p_linked_n t t_1 a_3 a_2
           (i + i_1) (&1:int) a_1`;;
