(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_post_Unique_goal8:
  uniqueness of the list-node pointers at two distinct array indices after
  the array-pop memory havoc, under the linked-list and memory invariants.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !t_2 t_3:(int#int)->(int#int).
   !a_4:int#int.
   !i_2 i:int.
   !a_1:int#int.
   !i_5 i_1 i_4 i_3:int.
   !a a_3:int#int.
   !t:int->int.
   !a_2:int#int.
   !t_1:(int#int)->real.
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
     let havoc =
       \(m0:(int#int)->(int#int))
        (m1:(int#int)->(int#int))
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let p_array_swipe_left =
       \(mptr0:(int#int)->(int#int))
        (mptr1:(int#int)->(int#int))
        (array:int#int) (down:int) (up:int).
         !j:int.
           down <= j
           ==> j < up
           ==> mptr1 (shift array ((&1:int) + j)) =
               mptr0 (shift array j) in
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
     let a_5 =
       havoc t_2 t_3 (shift a_4 i_2) (i - (&1:int)) in
     let a_6 = t_3 a_1 in
     let x = i + i_2 in
     let x_1 = (&1:int) + i_5 in
     let a_7 = shift a_4 (&0:int) in
     let a_8 = t_3 (shift a_4 i_1) in
     let x_2 = i_2 - i_1 in
     ~(i_4 = i_3)
     ==> a_5 a_1 = a_6
     ==> (&0:int) < i
     ==> (&0:int) <= i_1
     ==> i_1 <= i_2
     ==> i_1 <= i_3
     ==> i_1 <= i_4
     ==> i_2 <= i_5
     ==> i_5 < x
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> region (FST a_4) <= (&0:int)
     ==> (&2:int) + i_3 <= x
     ==> (&2:int) + i_4 <= x
     ==> x <= x_1
     ==> framed t_3
     ==> linked t
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> is_sint32 i_5
     ==> valid_rw t a_7 (&2147483646:int)
     ==> separated a_1 (&1:int) a_7 (&2147483646:int)
     ==> separated a_6 (&4:int) a_7 (&2147483646:int)
     ==> p_linked_n t t_3 a a_4 i_2 i a_3
     ==> p_linked_n t t_3 a_8 a_4 i_1 x_2 a
     ==> p_array_swipe_left a_5 t_3 a_4 i_2 i_5
     ==> p_linked_n t a_5 a_2 a_4 x_1
           (i + i_2 - (&1:int) - i_5) a_3
     ==> p_linked_n t a_5 a_8 a_4 i_1 x_2 a
     ==> p_linked_n t a_5 (a_5 (shift a (&0:int))) a_4 i_2
           (i_5 - i_2) a_2
     ==> p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_1 i_2
     ==> p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_5 x
     ==> (!i_6:int.
            i_1 <= i_6
            ==> i_6 < x
            ==> separated a_1 (&1:int)
                  (t_3 (shift a_4 i_6)) (&4:int))
     ==> (!i_6:int.
            i_1 <= i_6
            ==> i_6 < x
            ==> separated (t_3 (shift a_4 i_6)) (&4:int)
                  a_7 (&2147483646:int))
     ==> (!i_7 i_6:int.
            ~(i_7 = i_6)
            ==> i_1 <= i_6
            ==> i_1 <= i_7
            ==> i_6 < x
            ==> i_7 < x
            ==> ~(t_3 (shift a_4 i_7) =
                    t_3 (shift a_4 i_6)))
     ==> (!i_7 i_6:int.
            ~(i_7 = i_6)
            ==> i_1 <= i_6
            ==> i_1 <= i_7
            ==> i_6 < x
            ==> i_7 < x
            ==> separated (t_3 (shift a_4 i_7)) (&4:int)
                  (t_3 (shift a_4 i_6)) (&4:int))
     ==> ~(a_5 (shift a_4 i_4) =
           a_5 (shift a_4 i_3))`;;
