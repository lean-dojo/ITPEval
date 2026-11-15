(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_tail_pre_2_part4_goal33:
  preservation of a linked-list segment after searching, shifting, havocing,
  and updating pointer memory while adding a Contiki list item. This file
  contains no proof.
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
     let update =
       \(f:(int#int)->(int#int))
        (p:int#int) (v:int#int) (q:int#int).
         if q = p then v else f q in
     let havoc =
       \(m0:(int#int)->(int#int))
        (m1:(int#int)->(int#int))
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let eqs1_list_load =
       \(p0:int#int)
        (mflt0:(int#int)->real)
        (mptr0:(int#int)->(int#int))
        (p1:int#int)
        (mflt1:(int#int)->real)
        (mptr1:(int#int)->(int#int)).
         mptr1 (shift p1 (&0:int)) =
           mptr0 (shift p0 (&0:int)) /\
         mflt1 (shift p1 (&1:int)) =
           mflt0 (shift p0 (&1:int)) /\
         mflt1 (shift p1 (&2:int)) =
           mflt0 (shift p0 (&2:int)) /\
         mflt1 (shift p1 (&3:int)) =
           mflt0 (shift p0 (&3:int)) in
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
     ==> !t_3:(int#int)->(int#int).
         !a_3:int#int.
         !i_2 i i_1:int.
         !t_2:(int#int)->(int#int).
         !a_2 a a_1:int#int.
         !t:int->int.
         !t_1:(int#int)->real.
           let a_4 = t_3 (shift a_3 i_2) in
           let x = (&1:int) + i + i_1 in
           let x_1 = l_index_of t_3 a_4 a_3 i_1 x in
           let x_2 = x_1 - (&1:int) in
           let a_5 = shift a_3 x_2 in
           let a_6 = t_3 a_5 in
           let a_7 =
             havoc t_2
               (update
                 (update t_3 a_2 a)
                 (shift a_6 (&0:int)) a_1)
               (shift a_3 x_1)
               ((&1:int) + i + i_1 - x_1) in
           let a_8 =
             update a_7 (shift a_4 (&0:int))
               ((&0:int),(&0:int)) in
           let a_9 = a_8 a_2 in
           let x_4 = i + i_1 in
           let x_5 = (&1:int) + i in
           let a_11 = shift a_3 (&0:int) in
           let a_12 = t_3 a_2 in
           let a_13 = a_7 a_2 in
           ~(a_4 = ((&0:int),(&0:int)))
           ==> ~(x = x_1)
           ==> ~(a_9 = ((&0:int),(&0:int)))
           ==> (&0:int) <= i_1
           ==> i_1 <= i_2
           ==> i_2 <= x_4
           ==> region (FST a_2) <= (&0:int)
           ==> region (FST a_3) <= (&0:int)
           ==> region (FST a_4) <= (&0:int)
           ==> i_1 <= x_1
           ==> x_1 <= x_4
           ==> --(&1:int) <= i
           ==> i <= (&2147483644:int)
           ==> i_1 <= (&2147483645:int)
           ==> x_4 <= (&2147483644:int)
           ==> x_1 <= x
           ==> framed t_3
           ==> linked t
           ==> is_sint32 i
           ==> is_sint32 i_1
           ==> valid_rw t a_2 (&1:int)
           ==> is_sint32 x_5
           ==> valid_rw t a_11 (&2147483646:int)
           ==> valid_rw t (shift a_3 i_1) x_5
           ==> valid_rw t a_4 (&4:int)
           ==> separated a_2 (&1:int)
                 a_11 (&2147483646:int)
           ==> separated a_12 (&4:int)
                 a_11 (&2147483646:int)
           ==> separated a_2 (&1:int) a_4 (&4:int)
           ==> separated a_4 (&4:int)
                 a_11 (&2147483646:int)
           ==> p_linked_n t t_3 a_12 a_3 i_1 x_5
                 ((&0:int),(&0:int))
           ==> is_sint32 x_1
           ==> separated a_13 (&4:int)
                 a_11 (&2147483646:int)
           ==> eqs1_list_load a_4 t_1 a_7 a_4 t_1 t_3
           ==> (i_1 < x_1
                ==> (?i_3:int.
                       a_4 = t_3 (shift a_3 i_3) /\
                       i_1 <= i_3 /\ i_3 <= x_4)
                ==> a_7 a_5 = a_6)
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> p_array_swipe_left a_7 t_3 a_3 x_1 x_4)
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 < x_4
                       ==> ~(a_7 (shift a_3 i_3) = a_4)))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 <= x_4
                       ==> ~(a_7 (shift a_3 i_3) = a_4)))
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> p_linked_n t a_7 a_13 a_3 i_1 i
                      ((&0:int),(&0:int)))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> p_linked_n t a_7 a_13 a_3 i_1 x_5
                      ((&0:int),(&0:int)))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> p_unchanged t a_7 t_1 t t_3 t_1
                      a_3 i_1 x)
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> p_unchanged t a_7 t_1 t t_3 t_1
                      a_3 i_1 x_2)
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 < x_4
                       ==> separated a_2 (&1:int)
                             (a_7 (shift a_3 i_3)) (&4:int)))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 <= x_4
                       ==> separated a_2 (&1:int)
                             (a_7 (shift a_3 i_3)) (&4:int)))
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 < x_4
                       ==> separated a_4 (&4:int)
                             (a_7 (shift a_3 i_3)) (&4:int)))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 <= x_4
                       ==> separated a_4 (&4:int)
                             (a_7 (shift a_3 i_3)) (&4:int)))
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 < x_4
                       ==> separated (a_7 (shift a_3 i_3))
                             (&4:int) a_11
                             (&2147483646:int)))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> (!i_3:int.
                       i_1 <= i_3
                       ==> i_3 <= x_4
                       ==> separated (a_7 (shift a_3 i_3))
                             (&4:int) a_11
                             (&2147483646:int)))
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> (!i_3:int.
                       i_3 < x_4
                       ==> x_1 <= i_3
                       ==> eqs1_list_load
                             (a_7 (shift a_3 i_3)) t_1 a_7
                             (t_3 (shift a_3 ((&1:int) + i_3)))
                             t_1 t_3))
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> (!i_4 i_3:int.
                       ~(i_4 = i_3)
                       ==> i_1 <= i_3
                       ==> i_1 <= i_4
                       ==> i_3 < x_4
                       ==> i_4 < x_4
                       ==> ~(a_7 (shift a_3 i_4) =
                             a_7 (shift a_3 i_3))))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> (!i_4 i_3:int.
                       ~(i_4 = i_3)
                       ==> i_1 <= i_3
                       ==> i_1 <= i_4
                       ==> i_3 <= x_4
                       ==> i_4 <= x_4
                       ==> ~(a_7 (shift a_3 i_4) =
                             a_7 (shift a_3 i_3))))
           ==> ((?i_3:int.
                  a_4 = t_3 (shift a_3 i_3) /\
                  i_1 <= i_3 /\ i_3 <= x_4)
                ==> (!i_4 i_3:int.
                       ~(i_4 = i_3)
                       ==> i_1 <= i_3
                       ==> i_1 <= i_4
                       ==> i_3 < x_4
                       ==> i_4 < x_4
                       ==> separated (a_7 (shift a_3 i_4))
                             (&4:int)
                             (a_7 (shift a_3 i_3)) (&4:int)))
           ==> ((!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> ~(a_4 = t_3 (shift a_3 i_3)))
                ==> (!i_4 i_3:int.
                       ~(i_4 = i_3)
                       ==> i_1 <= i_3
                       ==> i_1 <= i_4
                       ==> i_3 <= x_4
                       ==> i_4 <= x_4
                       ==> separated (a_7 (shift a_3 i_4))
                             (&4:int)
                             (a_7 (shift a_3 i_3)) (&4:int)))
           ==> (!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> separated a_2 (&1:int)
                        (t_3 (shift a_3 i_3)) (&4:int))
           ==> (!i_3:int.
                  i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> separated (t_3 (shift a_3 i_3))
                        (&4:int) a_11 (&2147483646:int))
           ==> (!i_3:int.
                  let a_14 = t_3 (shift a_3 i_3) in
                  ~(a_4 = a_14)
                  ==> i_1 <= i_3
                  ==> i_3 <= x_4
                  ==> separated a_4 (&4:int) a_14 (&4:int))
           ==> (!i_4 i_3:int.
                  ~(i_4 = i_3)
                  ==> i_1 <= i_3
                  ==> i_1 <= i_4
                  ==> i_3 <= x_4
                  ==> i_4 <= x_4
                  ==> ~(t_3 (shift a_3 i_4) =
                        t_3 (shift a_3 i_3)))
           ==> (!i_4 i_3:int.
                  ~(i_4 = i_3)
                  ==> i_1 <= i_3
                  ==> i_1 <= i_4
                  ==> i_3 <= x_4
                  ==> i_4 <= x_4
                  ==> separated (t_3 (shift a_3 i_4))
                        (&4:int)
                        (t_3 (shift a_3 i_3)) (&4:int))
           ==> p_linked_n t a_8 a_9 a_3 i_1 i
                 ((&0:int),(&0:int))`;;
