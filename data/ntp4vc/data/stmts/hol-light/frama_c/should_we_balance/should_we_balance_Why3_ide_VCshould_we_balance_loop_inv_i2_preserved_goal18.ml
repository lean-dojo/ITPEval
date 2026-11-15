(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_i2_preserved_goal18:
  preservation of a scheduler load-balancing loop invariant asserting that
  the earlier selected CPU is idle, under the stated integer bounds, memory
  validity, framing, separation, CPU-mask layout, and search hypotheses.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_size:int.
   !l_idle_cpu:int->int.
   !l_sched_group_cpus:(int#int)->(int#int).
   !l_sched_group_mask:(int#int)->(int#int).
   !l_group_balance_mask:(int#int)->(int#int).
   !l_cpu_smt_mask:int->(int#int).
   !a_1:int#int.
   !t_3:(int#int)->int.
   !t_4:(int#int)->(int#int).
   !a:int#int.
   !i:int.
   !t_2 t_1:(int#int)->int.
   !i_2 i_3 i_1:int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let valid_rd =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST p) /\
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
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let to_uint32 =
       \z:int. z rem (&4294967296:int) in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let a_2 = shift a_1 (&3:int) in
     let x = t_3 a_2 in
     let a_3 = shift a_1 (&4:int) in
     let a_4 = t_4 a_3 in
     let a_5 = shift a_4 (&0:int) in
     let a_6 = t_4 a_5 in
     let a_7 = shift a_1 (&1:int) in
     let x_1 = t_3 a_7 in
     let x_2 = t_3 (shift a_6 x_1) in
     let a_8 = shift a i in
     let a_9 = shift a_8 (&0:int) in
     let a_10 = t_4 a_9 in
     let a_11 = shift a_10 (&0:int) in
     let a_12 = havoc t_2 t_3 a_11 l_size in
     let a_13 = shift a_1 (&0:int) in
     let a_14 = t_4 a_13 in
     let a_15 = shift a_14 (&0:int) in
     let a_16 = t_4 a_15 in
     let a_17 = l_group_balance_mask a_16 in
     let a_18 = t_4 (shift a_17 (&0:int)) in
     let a_19 = shift a_14 (&1:int) in
     let a_20 = shift a_6 (&0:int) in
     let a_21 = havoc t_1 t_3 a_11 l_size in
     let a_22 = shift a_6 (--(&1:int)) in
     let a_23 = shift a_18 (--(&1:int)) in
     let a_24 = a_12 (shift a_10 i_2) in
     let a_25 = a_12 (shift a_6 i_2) in
     let a_26 = shift a_18 (&0:int) in
     let x_3 = to_uint32 i_3 in
     ((&0:int) < l_size /\ l_size <= (&2147483647:int))
     ==> (!i_1:int.
            !mint:(int#int)->int.
            !mptr:(int#int)->(int#int).
              (&0:int) <= i_1
              ==> i_1 < l_size
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask i_1) (&0:int)))
                        i_1) =
                    (&0:int)))
     ==> (!mint:(int#int)->int.
            !mptr:(int#int)->(int#int).
            !j i_1:int.
              ~(mint
                  (shift
                    (mptr (shift (l_cpu_smt_mask j) (&0:int)))
                    i_1) =
                (&0:int))
              ==> (&0:int) <= i_1
              ==> i_1 < l_size
              ==> (&0:int) <= j
              ==> j < l_size
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask i_1) (&0:int)))
                        j) =
                    (&0:int)))
     ==> (!mptr:(int#int)->(int#int).
            !i_1:int.
            !mint:(int#int)->int.
            !j k:int.
              ~(mint
                  (shift
                    (mptr
                      (shift (l_cpu_smt_mask i_1) (&0:int)))
                    j) =
                (&0:int))
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask j) (&0:int)))
                        k) =
                    (&0:int))
              ==> (&0:int) <= i_1
              ==> i_1 < l_size
              ==> (&0:int) <= j
              ==> j < l_size
              ==> (&0:int) <= k
              ==> k < l_size
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask i_1) (&0:int)))
                        k) =
                    (&0:int)))
     ==> (!j:int. is_uint8 (l_idle_cpu j))
     ==> l_idle_cpu i_2 = (&0:int)
     ==> ~(x = (&2:int))
     ==> ~(x_2 = (&0:int))
     ==> ~(a_12 (shift a_6 i_1) = (&0:int))
     ==> ~(a_12 (shift a_18 i_1) = (&0:int))
     ==> (&0:int) <= i
     ==> i < l_size
     ==> (&0:int) <= i_1
     ==> i_1 < l_size
     ==> (&0:int) <= i_2
     ==> i_1 <= i_2
     ==> i_2 < l_size
     ==> (&0:int) <= i_3
     ==> i_3 <= l_size
     ==> to_uint32 i_2 < l_size
     ==> (&0:int) <= x_1
     ==> x_1 < l_size
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> i_2 <= (&2147483646:int)
     ==> framed t_4
     ==> linked t
     ==> is_uint32 i
     ==> is_sint32 i_2
     ==> is_sint32 i_3
     ==> valid_rd t a_1 (&5:int)
     ==> is_uint32 x
     ==> is_sint32 ((&1:int) + i_2)
     ==> is_sint32 x_1
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_7 (&1:int)
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_13 (&1:int)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rd t a_4 (&1:int)
     ==> valid_rd t (t_4 (shift a_1 (&2:int))) (&2:int)
     ==> valid_rd t a_14 (&2:int)
     ==> is_sint32 (t_3 a_19)
     ==> valid_rd t a_9 (&1:int)
     ==> valid_rd t a_5 (&1:int)
     ==> valid_rd t a_15 (&1:int)
     ==> valid_rd t a_16 (&1:int)
     ==> valid_rd t a_17 (&1:int)
     ==> is_uint8 x_2
     ==> valid_rd t a_11 l_size
     ==> valid_rd t a_20 l_size
     ==> valid_rw t a_11 l_size
     ==> is_uint8 (a_21 a_22)
     ==> is_uint8 (a_21 a_23)
     ==> is_uint8 a_24
     ==> is_uint8 (a_12 a_22)
     ==> is_uint8 a_25
     ==> is_uint8 (a_12 a_23)
     ==> is_sint32 (a_21 a_19)
     ==> is_sint32 (a_12 a_19)
     ==> valid_rd t a_26 l_size
     ==> separated a_11 l_size a_26 l_size
     ==> ((?i_4:int.
             ~(a_12 (shift a_10 i_4) = (&0:int)) /\
             ~(a_12 (shift a_6 i_4) = (&0:int)) /\
             i_4 < l_size /\
             x_3 <= i_4)
          ==> x_3 <= i_2)
     ==> ((?i_4:int.
             ~(a_12 (shift a_10 i_4) = (&0:int)) /\
             ~(a_12 (shift a_6 i_4) = (&0:int)) /\
             i_4 < l_size /\
             x_3 <= i_4)
          ==> ~(a_24 = (&0:int)) /\
              ~(a_25 = (&0:int)))
     ==> ((!i_4:int.
             i_4 < l_size
             ==> x_3 <= i_4
             ==> a_12 (shift a_10 i_4) = (&0:int) \/
                 a_12 (shift a_6 i_4) = (&0:int))
          ==> l_size = i_2)
     ==> ((?i_4:int.
             ~(a_12 (shift a_10 i_4) = (&0:int)) /\
             ~(a_12 (shift a_6 i_4) = (&0:int)) /\
             i_4 < l_size /\
             x_3 <= i_4)
          ==> (!i_4:int.
                 i_4 < i_2
                 ==> x_3 <= i_4
                 ==> a_12 (shift a_10 i_4) = (&0:int) \/
                     a_12 (shift a_6 i_4) = (&0:int)))
     ==> (!i_4:int.
            (&0:int) <= i_4
            ==> i_4 < l_size
            ==> separated a_20 l_size
                  (shift
                    (t_4 (shift (shift a i_4) (&0:int)))
                    (&0:int))
                  l_size)
     ==> (!i_4:int.
            let a_27 = shift a i_4 in
            (&0:int) <= i_4
            ==> i_4 < l_size
            ==> valid_rd t a_27 (&1:int) /\
                valid_rw t
                  (shift (t_4 (shift a_27 (&0:int))) (&0:int))
                  l_size)
     ==> (!i_4:int.
            (&0:int) <= i_4
            ==> i_4 < l_size
            ==> (~(a_21 (shift a_18 i_4) = (&0:int)) <=>
                 ~(a_21 (shift a_10 i_4) = (&0:int))))
     ==> (!i_4:int.
            ~(a_12 (shift a_18 i_4) = (&0:int))
            ==> (&0:int) <= i_4
            ==> i_4 < l_size
            ==> ~(a_12 (shift a_10 i_4) = (&0:int)))
     ==> (!i_4:int.
            ~(a_12 (shift a_10 i_4) = (&0:int))
            ==> (&0:int) <= i_4
            ==> i_4 < l_size
            ==> ~(a_12 (shift a_18 i_4) = (&0:int)))
     ==> (!i_4:int.
            ~(a_12 (shift a_6 i_4) = (&0:int))
            ==> ~(a_12 (shift a_18 i_4) = (&0:int))
            ==> (&0:int) <= i_4
            ==> i_4 < i_3
            ==> i_4 < l_size
            ==> l_idle_cpu i_4 = (&0:int))
     ==> (!a_27:int#int.
            let a_28 = l_sched_group_cpus a_27 in
            let a_29 =
              shift (t_4 (shift a_28 (&0:int))) (&0:int) in
            valid_rd t a_28 (&1:int) /\
            valid_rd t a_29 l_size /\
            (!i_4:int.
               (&0:int) <= i_4
               ==> i_4 < l_size
               ==> separated a_29 l_size
                     (shift
                       (t_4 (shift (shift a i_4) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_27:int#int.
            let a_28 = l_sched_group_mask a_27 in
            let a_29 =
              shift (t_4 (shift a_28 (&0:int))) (&0:int) in
            valid_rd t a_28 (&1:int) /\
            valid_rd t a_29 l_size /\
            (!i_4:int.
               (&0:int) <= i_4
               ==> i_4 < l_size
               ==> separated a_29 l_size
                     (shift
                       (t_4 (shift (shift a i_4) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_27:int#int.
            let a_28 = l_group_balance_mask a_27 in
            let a_29 =
              shift (t_4 (shift a_28 (&0:int))) (&0:int) in
            valid_rd t a_28 (&1:int) /\
            valid_rd t a_29 l_size /\
            (!i_4:int.
               (&0:int) <= i_4
               ==> i_4 < l_size
               ==> separated a_29 l_size
                     (shift
                       (t_4 (shift (shift a i_4) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_4:int.
            let a_27 = l_cpu_smt_mask i_4 in
            let a_28 =
              shift (t_4 (shift a_27 (&0:int))) (&0:int) in
            (&0:int) <= i_4
            ==> i_4 < l_size
            ==> valid_rd t a_27 (&1:int) /\
                valid_rd t a_28 l_size /\
                (!i_5:int.
                   (&0:int) <= i_5
                   ==> i_5 < l_size
                   ==> separated a_28 l_size
                         (shift
                           (t_4
                             (shift (shift a i_5) (&0:int)))
                           (&0:int))
                         l_size))
     ==> l_idle_cpu i_1 = (&0:int)`;;
