(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_not_newly_idle_with_idle_cpu_post_2_goal39:
  the postcondition relating the selected CPU to the idle indicator in the
  not-newly-idle branch with an idle CPU, under the stated integer bounds,
  memory validity, framing, separation, CPU-mask layout, and search
  hypotheses. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_size:int.
   !l_idle_cpu:int->int.
   !l_sched_group_cpus:(int#int)->(int#int).
   !l_sched_group_mask:(int#int)->(int#int).
   !l_group_balance_mask:(int#int)->(int#int).
   !l_group_balance_cpu:(int#int)->int.
   !l_cpu_smt_mask:int->(int#int).
   !a_1:int#int.
   !t_7:(int#int)->int.
   !t_8:(int#int)->(int#int).
   !a:int#int.
   !i:int.
   !t_6:(int#int)->int.
   !i_8 i_3 i_9:int.
   !t_5:(int#int)->int.
   !i_5 i_6:int.
   !t:int->int.
   !i_1 i_2 i_4 i_7 i_10:int.
   !t_4 t_1 t_2 t_3:int->int.
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
     let bit_and_7 =
       \z:int. z rem (&8:int) in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let p_idle_core =
       \(mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (cpu:int).
         !j:int.
           ~(mint
               (shift
                 (mptr (shift (l_cpu_smt_mask cpu) (&0:int)))
                 j) =
             (&0:int))
           ==> (&0:int) <= j
           ==> j < l_size
           ==> ~(l_idle_cpu j = (&0:int)) in
     let a_2 = shift a_1 (&3:int) in
     let x = t_7 a_2 in
     let a_3 = shift a_1 (&0:int) in
     let a_4 = t_8 a_3 in
     let a_5 = shift a_4 (&1:int) in
     let x_1 = t_7 a_5 in
     let a_6 = shift a_1 (&4:int) in
     let a_7 = t_8 a_6 in
     let a_8 = shift a_7 (&0:int) in
     let a_9 = t_8 a_8 in
     let a_10 = shift a_1 (&1:int) in
     let x_2 = t_7 a_10 in
     let x_3 = t_7 (shift a_9 x_2) in
     let a_11 = shift a_4 (&0:int) in
     let a_12 = t_8 a_11 in
     let a_13 = l_group_balance_mask a_12 in
     let a_14 = t_8 (shift a_13 (&0:int)) in
     let a_15 = shift a i in
     let a_16 = shift a_15 (&0:int) in
     let a_17 = t_8 a_16 in
     let a_18 = shift a_17 (&0:int) in
     let a_19 = shift a_9 (&0:int) in
     let a_20 = havoc t_6 t_7 a_18 l_size in
     let a_21 = a_20 (shift a_17 i_8) in
     let a_22 = a_20 (shift a_9 i_3) in
     let a_23 = a_20 (shift a_9 i_8) in
     let a_24 = a_20 (shift a_14 i_3) in
     let a_25 = a_20 a_5 in
     let a_26 = shift a_14 (&0:int) in
     let a_27 = a_20 a_10 in
     let x_4 = bit_and_7 a_25 in
     let x_5 = to_uint32 i_9 in
     let a_28 = havoc t_5 t_7 a_18 l_size in
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
     ==> ~(l_idle_cpu i_5 = (&0:int))
     ==> ~(l_idle_cpu i_6 = (&0:int))
     ==> ~(x = (&2:int))
     ==> bit_and_7 x_1 = (&0:int)
     ==> ~(t_7 (shift a_9 i_5) = (&0:int))
     ==> ~(t_7 (shift a_9 i_6) = (&0:int))
     ==> ~(x_3 = (&0:int))
     ==> ~(t_7 (shift a_14 i_5) = (&0:int))
     ==> ~(t_7 (shift a_14 i_6) = (&0:int))
     ==> (&0:int) <= i
     ==> i < l_size
     ==> (&0:int) <= i_5
     ==> i_5 < l_size
     ==> (&0:int) <= i_6
     ==> i_6 < l_size
     ==> (&0:int) <= i_9
     ==> i_9 <= l_size
     ==> (&0:int) <= x_2
     ==> x_2 < l_size
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> framed t_8
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_sint32 i_2
     ==> is_sint32 i_3
     ==> is_sint32 i_4
     ==> is_sint32 i_7
     ==> is_sint32 i_8
     ==> is_sint32 i_9
     ==> is_sint32 i_10
     ==> valid_rd t a_1 (&5:int)
     ==> is_uint32 x
     ==> is_sint32 x_2
     ==> valid_rd t a_6 (&1:int)
     ==> valid_rd t a_10 (&1:int)
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_15 (&1:int)
     ==> valid_rd t a_7 (&1:int)
     ==> valid_rd t (t_8 (shift a_1 (&2:int))) (&2:int)
     ==> valid_rd t a_4 (&2:int)
     ==> is_sint32 x_1
     ==> valid_rd t a_16 (&1:int)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rd t a_11 (&1:int)
     ==> valid_rd t a_12 (&1:int)
     ==> valid_rd t a_13 (&1:int)
     ==> is_uint8 x_3
     ==> valid_rd t a_18 l_size
     ==> valid_rd t a_19 l_size
     ==> valid_rw t a_18 l_size
     ==> is_uint8 a_21
     ==> is_uint8 a_22
     ==> is_uint8 a_23
     ==> is_uint8 a_24
     ==> is_sint32 a_25
     ==> valid_rd t a_26 l_size
     ==> separated a_18 l_size a_26 l_size
     ==> (if to_uint32 i_8 < l_size
          then i_10 = i_8 /\
               t_4 = t /\
               ~(l_idle_cpu i_10 = (&0:int)) /\
               (if a_27 = i_10 then (&1:int) else (&0:int)) = i_2 /\
               (&0:int) <= i_10 /\
               i_10 < l_size /\
               valid_rd t_4 a_10 (&1:int) /\
               valid_rd t_4 a_3 (&1:int) /\
               valid_rd t_4 a_5 (&1:int) /\
               (~(x_4 = (&0:int)) \/
                l_size = i_1 /\
                p_idle_core t_8 (havoc t_6 t_7 a_18 i_1) i_10 /\
                (!i_11:int.
                   let a_29 = shift a i_11 in
                   (&0:int) <= i_11
                   ==> i_11 < i_1
                   ==> valid_rd t_4 a_29 (&1:int) /\
                       valid_rw t_4
                         (shift
                           (t_8 (shift a_29 (&0:int)))
                           (&0:int))
                         i_1) /\
                (!a_29:int#int.
                   let a_30 = l_sched_group_cpus a_29 in
                   let a_31 =
                     shift
                       (t_8 (shift a_30 (&0:int)))
                       (&0:int) in
                   valid_rd t_4 a_30 (&1:int) /\
                   valid_rd t_4 a_31 i_1 /\
                   (!i_11:int.
                      (&0:int) <= i_11
                      ==> i_11 < i_1
                      ==> separated a_31 i_1
                            (shift
                              (t_8
                                (shift
                                  (shift a i_11)
                                  (&0:int)))
                              (&0:int))
                            i_1)) /\
                (!a_29:int#int.
                   let a_30 = l_sched_group_mask a_29 in
                   let a_31 =
                     shift
                       (t_8 (shift a_30 (&0:int)))
                       (&0:int) in
                   valid_rd t_4 a_30 (&1:int) /\
                   valid_rd t_4 a_31 i_1 /\
                   (!i_11:int.
                      (&0:int) <= i_11
                      ==> i_11 < i_1
                      ==> separated a_31 i_1
                            (shift
                              (t_8
                                (shift
                                  (shift a i_11)
                                  (&0:int)))
                              (&0:int))
                            i_1)) /\
                (!a_29:int#int.
                   let a_30 = l_group_balance_mask a_29 in
                   let a_31 =
                     shift
                       (t_8 (shift a_30 (&0:int)))
                       (&0:int) in
                   valid_rd t_4 a_30 (&1:int) /\
                   valid_rd t_4 a_31 i_1 /\
                   (!i_11:int.
                      (&0:int) <= i_11
                      ==> i_11 < i_1
                      ==> separated a_31 i_1
                            (shift
                              (t_8
                                (shift
                                  (shift a i_11)
                                  (&0:int)))
                              (&0:int))
                            i_1)) /\
                (!i_11:int.
                   let a_29 = l_cpu_smt_mask i_11 in
                   let a_30 =
                     shift
                       (t_8 (shift a_29 (&0:int)))
                       (&0:int) in
                   (&0:int) <= i_11
                   ==> i_11 < i_1
                   ==> valid_rd t_4 a_29 (&1:int) /\
                       valid_rd t_4 a_30 i_1 /\
                       (!i_12:int.
                          (&0:int) <= i_12
                          ==> i_12 < i_1
                          ==> separated a_30 i_1
                                (shift
                                  (t_8
                                    (shift
                                      (shift a i_12)
                                      (&0:int)))
                                  (&0:int))
                                i_1)))
          else i_4 = i_3 /\
               t_1 = t /\
               (if i_4 = --(&1:int)
                then t_2 = t_1 /\
                     l_group_balance_cpu a_12 = i_7 /\
                     (if a_27 = i_7
                      then (&1:int)
                      else (&0:int)) = i_2 /\
                     valid_rd t_2 a_10 (&1:int)
                else t_3 = t_1 /\
                     (if a_27 = i_4
                      then (&1:int)
                      else (&0:int)) = i_2 /\
                     valid_rd t_3 a_10 (&1:int)))
     ==> (~(x_4 = (&0:int))
          ==> i_3 = --(&1:int))
     ==> (~(i_3 = --(&1:int))
          ==> ~(l_idle_cpu i_3 = (&0:int)) /\
              ~(a_22 = (&0:int)) /\
              ~(a_24 = (&0:int)) /\
              (&0:int) <= i_3 /\
              i_3 < l_size)
     ==> (i_3 = --(&1:int)
          ==> (!i_11:int.
                 ~(a_20 (shift a_14 i_11) = (&0:int))
                 ==> (&0:int) <= i_11
                 ==> i_11 < l_size
                 ==> ~(a_20 (shift a_17 i_11) = (&0:int))))
     ==> ((?i_11:int.
             ~(a_20 (shift a_17 i_11) = (&0:int)) /\
             ~(a_20 (shift a_9 i_11) = (&0:int)) /\
             i_11 < l_size /\
             x_5 <= i_11)
          ==> i_8 < l_size)
     ==> ((?i_11:int.
             ~(a_20 (shift a_17 i_11) = (&0:int)) /\
             ~(a_20 (shift a_9 i_11) = (&0:int)) /\
             i_11 < l_size /\
             x_5 <= i_11)
          ==> i_8 < l_size /\
              x_5 <= i_8)
     ==> ((?i_11:int.
             ~(a_20 (shift a_17 i_11) = (&0:int)) /\
             ~(a_20 (shift a_9 i_11) = (&0:int)) /\
             i_11 < l_size /\
             x_5 <= i_11)
          ==> ~(a_21 = (&0:int)) /\
              ~(a_23 = (&0:int)))
     ==> ((!i_11:int.
             i_11 < l_size
             ==> x_5 <= i_11
             ==> a_20 (shift a_17 i_11) = (&0:int) \/
                 a_20 (shift a_9 i_11) = (&0:int))
          ==> l_size = i_8)
     ==> (~(i_3 = --(&1:int))
          ==> (!i_11:int.
                 ~(a_20 (shift a_9 i_11) = (&0:int))
                 ==> ~(a_20 (shift a_14 i_11) = (&0:int))
                 ==> (&0:int) <= i_11
                 ==> i_11 < i_3
                 ==> i_11 < l_size
                 ==> l_idle_cpu i_11 = (&0:int)))
     ==> (i_3 = --(&1:int)
          ==> (!i_11:int.
                 ~(a_20 (shift a_9 i_11) = (&0:int))
                 ==> ~(a_20 (shift a_14 i_11) = (&0:int))
                 ==> (&0:int) <= i_11
                 ==> i_11 < i_9
                 ==> i_11 < l_size
                 ==> l_idle_cpu i_11 = (&0:int)))
     ==> ((?i_11:int.
             ~(a_20 (shift a_17 i_11) = (&0:int)) /\
             ~(a_20 (shift a_9 i_11) = (&0:int)) /\
             i_11 < l_size /\
             x_5 <= i_11)
          ==> (!i_11:int.
                 i_11 < i_8
                 ==> x_5 <= i_11
                 ==> a_20 (shift a_17 i_11) = (&0:int) \/
                     a_20 (shift a_9 i_11) = (&0:int)))
     ==> (~(i_3 = --(&1:int))
          ==> (!i_11:int.
                 ~(a_20 (shift a_9 i_11) = (&0:int))
                 ==> ~(a_20 (shift a_14 i_11) = (&0:int))
                 ==> (&0:int) <= i_11
                 ==> i_3 <= i_11
                 ==> i_11 < i_9
                 ==> i_11 < l_size
                 ==> ~(p_idle_core t_8 a_20 i_11)))
     ==> (~(i_3 = --(&1:int))
          ==> (!i_11:int.
                 ~(a_20 (shift a_14 i_11) = (&0:int))
                 ==> (&0:int) <= i_11
                 ==> i_11 < l_size
                 ==> ~(a_20 (shift a_17 i_11) = (&0:int)) \/
                     ~(p_idle_core t_8 a_20 i_11)))
     ==> (!i_11:int.
            (&0:int) <= i_11
            ==> i_11 < l_size
            ==> separated a_19 l_size
                  (shift
                    (t_8
                      (shift
                        (shift a i_11)
                        (&0:int)))
                    (&0:int))
                  l_size)
     ==> (!i_11:int.
            let a_29 = shift a i_11 in
            (&0:int) <= i_11
            ==> i_11 < l_size
            ==> valid_rd t a_29 (&1:int) /\
                valid_rw t
                  (shift
                    (t_8 (shift a_29 (&0:int)))
                    (&0:int))
                  l_size)
     ==> (!i_11:int.
            (&0:int) <= i_11
            ==> i_11 < l_size
            ==> (~(a_28 (shift a_14 i_11) = (&0:int)) <=>
                 ~(a_28 (shift a_17 i_11) = (&0:int))))
     ==> (!i_11:int.
            ~(a_20 (shift a_17 i_11) = (&0:int))
            ==> (&0:int) <= i_11
            ==> i_11 < l_size
            ==> ~(a_20 (shift a_14 i_11) = (&0:int)))
     ==> (!i_11:int.
            ~(t_7 (shift a_9 i_11) = (&0:int))
            ==> ~(t_7 (shift a_14 i_11) = (&0:int))
            ==> (&0:int) <= i_11
            ==> i_11 < l_size
            ==> ~(p_idle_core t_8 t_7 i_11))
     ==> (!i_11:int.
            ~(t_7 (shift a_9 i_11) = (&0:int))
            ==> ~(t_7 (shift a_14 i_11) = (&0:int))
            ==> (&0:int) <= i_11
            ==> i_11 < i_6
            ==> i_11 < l_size
            ==> l_idle_cpu i_11 = (&0:int))
     ==> (!a_29:int#int.
            let a_30 = l_sched_group_cpus a_29 in
            let a_31 =
              shift (t_8 (shift a_30 (&0:int))) (&0:int) in
            valid_rd t a_30 (&1:int) /\
            valid_rd t a_31 l_size /\
            (!i_11:int.
               (&0:int) <= i_11
               ==> i_11 < l_size
               ==> separated a_31 l_size
                     (shift
                       (t_8
                         (shift
                           (shift a i_11)
                           (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_29:int#int.
            let a_30 = l_sched_group_mask a_29 in
            let a_31 =
              shift (t_8 (shift a_30 (&0:int))) (&0:int) in
            valid_rd t a_30 (&1:int) /\
            valid_rd t a_31 l_size /\
            (!i_11:int.
               (&0:int) <= i_11
               ==> i_11 < l_size
               ==> separated a_31 l_size
                     (shift
                       (t_8
                         (shift
                           (shift a i_11)
                           (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_29:int#int.
            let a_30 = l_group_balance_mask a_29 in
            let a_31 =
              shift (t_8 (shift a_30 (&0:int))) (&0:int) in
            valid_rd t a_30 (&1:int) /\
            valid_rd t a_31 l_size /\
            (!i_11:int.
               (&0:int) <= i_11
               ==> i_11 < l_size
               ==> separated a_31 l_size
                     (shift
                       (t_8
                         (shift
                           (shift a i_11)
                           (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_11:int.
            let a_29 = l_cpu_smt_mask i_11 in
            let a_30 =
              shift (t_8 (shift a_29 (&0:int))) (&0:int) in
            (&0:int) <= i_11
            ==> i_11 < l_size
            ==> valid_rd t a_29 (&1:int) /\
                valid_rd t a_30 l_size /\
                (!i_12:int.
                   (&0:int) <= i_12
                   ==> i_12 < l_size
                   ==> separated a_30 l_size
                         (shift
                           (t_8
                             (shift
                               (shift a i_12)
                               (&0:int)))
                           (&0:int))
                         l_size))
     ==> ((x_2 = i_6) <=> ~(i_2 = (&0:int)))`;;
