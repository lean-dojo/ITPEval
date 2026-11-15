(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_assign_part5_goal28:
  a list-removal memory-safety verification condition classifying the assigned
  pointer address under linked-list, framing, validity, and separation
  invariants. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_index_of:
      ((int#int)->(int#int))->
      (int#int)->(int#int)->int->int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let included =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         (&0:int) < n
         ==> (&0:int) <= m /\
             FST p = FST q /\
             SND q <= SND p /\
             SND p + n <= SND q + m in
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let invalid =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> malloc (FST p) <= SND p \/
             SND p + n <= (&0:int) in
     let framed =
       \(mptr:(int#int)->(int#int)).
         !p:int#int. region (FST (mptr p)) <= (&0:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_unchanged =
       \(malloc0:int->int)
        (mptr0:(int#int)->(int#int))
        (mflt0:(int#int)->real)
        (malloc1:int->int)
        (mptr1:(int#int)->(int#int))
        (mflt1:(int#int)->real)
        (array:int#int) (down:int) (up:int).
         !j:int.
           let q = shift array j in
           let q0 = mptr0 q in
           let q1 = mptr1 q in
           down <= j
           ==> j < up
           ==> q0 = q1 /\
               mptr0 (shift q0 (&0:int)) =
                 mptr1 (shift q1 (&0:int)) /\
               mflt0 (shift q0 (&1:int)) =
                 mflt1 (shift q1 (&1:int)) /\
               mflt0 (shift q0 (&2:int)) =
                 mflt1 (shift q1 (&2:int)) /\
               mflt0 (shift q0 (&3:int)) =
                 mflt1 (shift q1 (&3:int)) /\
               (valid_rw malloc1 q1 (&4:int)
                ==> valid_rw malloc0 q0 (&4:int)) in
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
     ==> !t_2:(int#int)->(int#int).
         !a_1 a:int#int.
         !i i_1:int.
         !a_2:int#int.
         !i_2:int.
         !t:int->int.
         !t_1:(int#int)->real.
           let a_3 = t_2 a_1 in
           let a_4 = shift a (&0:int) in
           let a_5 = t_2 a_4 in
           let x = i + i_1 in
           let a_6 = shift a_2 (&0:int) in
           let x_1 = l_index_of t_2 a_5 a_2 i_1 x in
           ~(a_3 = ((&0:int),(&0:int)))
           ==> ~(a_5 = ((&0:int),(&0:int)))
           ==> ~(a_5 = a_3)
           ==> (&0:int) <= i
           ==> (&0:int) <= i_1
           ==> i_1 <= i_2
           ==> i_2 <= x
           ==> region (FST a_1) <= (&0:int)
           ==> region (FST a_2) <= (&0:int)
           ==> region (FST a_5) <= (&0:int)
           ==> i <= (&2147483645:int)
           ==> framed t_2
           ==> linked t
           ==> is_sint32 i
           ==> is_sint32 i_1
           ==> is_sint32 i_2
           ==> valid_rw t a_1 (&1:int)
           ==> ~(invalid t a_4 (&1:int))
           ==> valid_rw t a_6 (&2147483646:int)
           ==> separated a_1 (&1:int)
                 a_6 (&2147483646:int)
           ==> separated a_3 (&4:int)
                 a_6 (&2147483646:int)
           ==> p_linked_n t t_2 a_3 a_2 i_1 i
                 ((&0:int),(&0:int))
           ==> p_unchanged t t_2 t_1 t t_2 t_1
                 a_2 i_1 i_2
           ==> is_sint32 x_1
           ==> p_linked_n t t_2 a a_2 i_2 (&1:int) a_5
           ==> p_linked_n t t_2 a_3 a_2 i_1
                 (i_2 - i_1) a
           ==> p_linked_n t t_2 a_5 a_2
                 ((&1:int) + i_2)
                 (i + i_1 - (&1:int) - i_2)
                 ((&0:int),(&0:int))
           ==> (!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= i_2
                  ==> ~(t_2 (shift a_2 i_3) = a_5))
           ==> (!i_3:int.
                  i_1 <= i_3
                  ==> i_3 < x
                  ==> separated a_1 (&1:int)
                        (t_2 (shift a_2 i_3)) (&4:int))
           ==> (!i_3:int.
                  i_1 <= i_3
                  ==> i_3 < i_2
                  ==> separated a_5 (&4:int)
                        (t_2 (shift a_2 i_3)) (&4:int))
           ==> (!i_3:int.
                  i_1 <= i_3
                  ==> i_3 < x
                  ==> separated (t_2 (shift a_2 i_3))
                        (&4:int) a_6 (&2147483646:int))
           ==> (!i_3:int.
                  let a_7 = t_2 (shift a_2 i_3) in
                  ~(a_7 = a_5)
                  ==> i_1 <= i_3
                  ==> i_3 < x
                  ==> separated a_5 (&4:int) a_7 (&4:int))
           ==> (!i_4 i_3:int.
                  ~(i_4 = i_3)
                  ==> i_1 <= i_3
                  ==> i_1 <= i_4
                  ==> i_3 < x
                  ==> i_4 < x
                  ==> ~(t_2 (shift a_2 i_4) =
                          t_2 (shift a_2 i_3)))
           ==> (!i_4 i_3:int.
                  ~(i_4 = i_3)
                  ==> i_1 <= i_3
                  ==> i_1 <= i_4
                  ==> i_3 < x
                  ==> i_4 < x
                  ==> separated (t_2 (shift a_2 i_4))
                        (&4:int) (t_2 (shift a_2 i_3))
                        (&4:int))
           ==> a_4 = a_1 \/
               shift
                 (t_2 (shift a_2 (x_1 - (&1:int))))
                 (&0:int) = a_4 \/
               included a_4 (&1:int)
                 (shift a_2 x_1) (i + i_1 - x_1)`;;
