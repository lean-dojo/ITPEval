(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_10_goal22:
  a scheduler load-balancing verification condition asserting readability of
  a one-cell CPU-related address, under the stated integer bounds, memory
  validity, framing, separation, CPU-mask, and search assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !bit_and:int->int->int.
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
   !t_1 t_2:(int#int)->int.
   !i_1 i_2:int.
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
     let x = t_3 a_2 in
     let a_3 = shift a_1 (&4:int) in
     let a_4 = t_4 a_3 in
     let a_5 = t_4 (shift a_4 (&0:int)) in
     let a_6 = shift a_1 (&1:int) in
     let x_1 = t_3 a_6 in
     let x_2 = t_3 (shift a_5 x_1) in
     let a_7 = shift a_1 (&0:int) in
     let a_8 = shift a i in
     let a_9 = t_4 a_7 in
     let a_10 = shift a_9 (&1:int) in
     let a_11 = shift a_9 (&0:int) in
     let a_12 = t_4 a_11 in
     let a_13 = l_group_balance_mask a_12 in
     let a_14 = shift a_5 (&0:int) in
     let a_15 = shift a_8 (&0:int) in
     let a_16 = t_4 a_15 in
     let a_17 = shift a_16 (&0:int) in
     let a_18 = havoc t_1 t_3 a_17 l_size in
     let a_19 = t_4 (shift a_13 (&0:int)) in
     let a_20 = havoc t_2 t_3 a_17 l_size in
     let a_21 = a_20 (shift a_5 i_1) in
     let a_22 = a_20 (shift a_19 i_1) in
     let a_23 = a_20 a_10 in
     let a_24 = shift a_19 (&0:int) in
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
     ==> ~(x = (&2:int))
     ==> ~(x_2 = (&0:int))
     ==> (&0:int) <= i
     ==> i < l_size
     ==> (&0:int) <= i_2
     ==> i_2 <= l_size
     ==> (&0:int) <= x_1
     ==> x_1 < l_size
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> framed t_4
     ==> linked t
     ==> is_uint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> valid_rd t a_1 (&5:int)
     ==> is_uint32 x
     ==> is_sint32 x_1
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_6 (&1:int)
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_7 (&1:int)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rd t a_4 (&1:int)
     ==> valid_rd t (t_4 (shift a_1 (&2:int))) (&2:int)
     ==> valid_rd t a_9 (&2:int)
     ==> is_sint32 (t_3 a_10)
     ==> valid_rd t a_11 (&1:int)
     ==> valid_rd t a_12 (&1:int)
     ==> valid_rd t a_13 (&1:int)
     ==> is_uint8 x_2
     ==> valid_rd t a_14 l_size
     ==> valid_rw t a_17 l_size
     ==> is_uint8 (a_18 (shift a_5 (--(&1:int))))
     ==> is_uint8 (a_18 (shift a_19 (--(&1:int))))
     ==> is_uint8 a_21
     ==> is_uint8 a_22
     ==> is_sint32 (a_18 a_10)
     ==> is_sint32 a_23
     ==> valid_rd t a_24 l_size
     ==> separated a_17 l_size a_24 l_size
     ==> (~(bit_and (&7:int) a_23 = (&0:int))
          ==> i_1 = --(&1:int))
     ==> (~(i_1 = --(&1:int))
          ==> ~(l_idle_cpu i_1 = (&0:int)) /\
              ~(a_21 = (&0:int)) /\
              ~(a_22 = (&0:int)) /\
              (&0:int) <= i_1 /\
              i_1 < l_size)
     ==> (i_1 = --(&1:int)
          ==> (!i_3:int.
                 ~(a_20 (shift a_19 i_3) = (&0:int))
                 ==> (&0:int) <= i_3
                 ==> i_3 < l_size
                 ==> ~(a_20 (shift a_16 i_3) = (&0:int))))
     ==> (~(i_1 = --(&1:int))
          ==> (!i_3:int.
                 ~(a_20 (shift a_5 i_3) = (&0:int))
                 ==> ~(a_20 (shift a_19 i_3) = (&0:int))
                 ==> (&0:int) <= i_3
                 ==> i_3 < i_1
                 ==> i_3 < l_size
                 ==> l_idle_cpu i_3 = (&0:int)))
     ==> (i_1 = --(&1:int)
          ==> (!i_3:int.
                 ~(a_20 (shift a_5 i_3) = (&0:int))
                 ==> ~(a_20 (shift a_19 i_3) = (&0:int))
                 ==> (&0:int) <= i_3
                 ==> i_3 < i_2
                 ==> i_3 < l_size
                 ==> l_idle_cpu i_3 = (&0:int)))
     ==> (~(i_1 = --(&1:int))
          ==> (!i_3:int.
                 ~(a_20 (shift a_5 i_3) = (&0:int))
                 ==> ~(a_20 (shift a_19 i_3) = (&0:int))
                 ==> (&0:int) <= i_3
                 ==> i_1 <= i_3
                 ==> i_3 < i_2
                 ==> i_3 < l_size
                 ==> ~(p_idle_core t_4 a_20 i_3)))
     ==> (~(i_1 = --(&1:int))
          ==> (!i_3:int.
                 ~(a_20 (shift a_19 i_3) = (&0:int))
                 ==> (&0:int) <= i_3
                 ==> i_3 < l_size
                 ==> ~(a_20 (shift a_16 i_3) = (&0:int)) \/
                     ~(p_idle_core t_4 a_20 i_3)))
     ==> (!i_3:int.
            (&0:int) <= i_3
            ==> i_3 < l_size
            ==> separated a_14 l_size
                  (shift
                    (t_4 (shift (shift a i_3) (&0:int)))
                    (&0:int))
                  l_size)
     ==> (!i_3:int.
            let a_25 = shift a i_3 in
            (&0:int) <= i_3
            ==> i_3 < l_size
            ==> valid_rd t a_25 (&1:int) /\
                valid_rw t
                  (shift (t_4 (shift a_25 (&0:int))) (&0:int))
                  l_size)
     ==> (!i_3:int.
            (&0:int) <= i_3
            ==> i_3 < l_size
            ==> (~(a_18 (shift a_19 i_3) = (&0:int)) <=>
                 ~(a_18 (shift a_16 i_3) = (&0:int))))
     ==> (!i_3:int.
            ~(a_20 (shift a_16 i_3) = (&0:int))
            ==> (&0:int) <= i_3
            ==> i_3 < l_size
            ==> ~(a_20 (shift a_19 i_3) = (&0:int)))
     ==> (!a_25:int#int.
            let a_26 = l_sched_group_cpus a_25 in
            let a_27 =
              shift (t_4 (shift a_26 (&0:int))) (&0:int) in
            valid_rd t a_26 (&1:int) /\
            valid_rd t a_27 l_size /\
            (!i_3:int.
               (&0:int) <= i_3
               ==> i_3 < l_size
               ==> separated a_27 l_size
                     (shift
                       (t_4 (shift (shift a i_3) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_25:int#int.
            let a_26 = l_sched_group_mask a_25 in
            let a_27 =
              shift (t_4 (shift a_26 (&0:int))) (&0:int) in
            valid_rd t a_26 (&1:int) /\
            valid_rd t a_27 l_size /\
            (!i_3:int.
               (&0:int) <= i_3
               ==> i_3 < l_size
               ==> separated a_27 l_size
                     (shift
                       (t_4 (shift (shift a i_3) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_25:int#int.
            let a_26 = l_group_balance_mask a_25 in
            let a_27 =
              shift (t_4 (shift a_26 (&0:int))) (&0:int) in
            valid_rd t a_26 (&1:int) /\
            valid_rd t a_27 l_size /\
            (!i_3:int.
               (&0:int) <= i_3
               ==> i_3 < l_size
               ==> separated a_27 l_size
                     (shift
                       (t_4 (shift (shift a i_3) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_3:int.
            let a_25 = l_cpu_smt_mask i_3 in
            let a_26 =
              shift (t_4 (shift a_25 (&0:int))) (&0:int) in
            (&0:int) <= i_3
            ==> i_3 < l_size
            ==> valid_rd t a_25 (&1:int) /\
                valid_rd t a_26 l_size /\
                (!i_4:int.
                   (&0:int) <= i_4
                   ==> i_4 < l_size
                   ==> separated a_26 l_size
                         (shift
                           (t_4
                             (shift (shift a i_4) (&0:int)))
                           (&0:int))
                         l_size))
     ==> valid_rd t a_15 (&1:int)`;;
