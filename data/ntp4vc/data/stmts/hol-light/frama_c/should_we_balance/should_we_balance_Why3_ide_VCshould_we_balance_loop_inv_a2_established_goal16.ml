(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_a2_established_goal16:
  establishment of a scheduler load-balancing loop invariant relating two
  views of an updated CPU mask under the stated bounds, memory-validity,
  framing, separation, and mask-layout hypotheses. This file contains no proof.
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
   !t_2:(int#int)->int.
   !t_3:(int#int)->(int#int).
   !a:int#int.
   !i:int.
   !t_1:(int#int)->int.
   !i_1:int.
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
     let a_2 = shift a_1 (&3:int) in
     let x = t_2 a_2 in
     let a_3 = shift a_1 (&4:int) in
     let a_4 = t_3 a_3 in
     let a_5 = t_3 (shift a_4 (&0:int)) in
     let a_6 = shift a_1 (&1:int) in
     let x_1 = t_2 a_6 in
     let x_2 = t_2 (shift a_5 x_1) in
     let a_7 = shift a i in
     let a_8 = t_3 (shift a_7 (&0:int)) in
     let a_9 = shift a_8 (&0:int) in
     let a_10 = havoc t_1 t_2 a_9 l_size in
     let a_11 = shift a_1 (&0:int) in
     let a_12 = t_3 a_11 in
     let a_13 = shift a_12 (&0:int) in
     let a_14 = t_3 a_13 in
     let a_15 = l_group_balance_mask a_14 in
     let a_16 = t_3 (shift a_15 (&0:int)) in
     let a_17 = shift a_5 (&0:int) in
     let a_18 = shift a_16 (&0:int) in
     ((&0:int) < l_size /\ l_size <= (&2147483647:int))
     ==> (!cpu:int. is_uint8 (l_idle_cpu cpu))
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
     ==> ~(x = (&2:int))
     ==> ~(x_2 = (&0:int))
     ==> ~(a_10 (shift a_16 i_1) = (&0:int))
     ==> (&0:int) <= i
     ==> i < l_size
     ==> (&0:int) <= i_1
     ==> i_1 < l_size
     ==> (&0:int) <= x_1
     ==> x_1 < l_size
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> framed t_3
     ==> linked t
     ==> is_uint32 i
     ==> valid_rd t a_1 (&5:int)
     ==> is_uint32 x
     ==> is_sint32 x_1
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_6 (&1:int)
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_11 (&1:int)
     ==> valid_rd t a_7 (&1:int)
     ==> valid_rd t a_4 (&1:int)
     ==> valid_rd t (t_3 (shift a_1 (&2:int))) (&2:int)
     ==> valid_rd t a_12 (&2:int)
     ==> is_sint32 (t_2 (shift a_12 (&1:int)))
     ==> valid_rd t a_13 (&1:int)
     ==> valid_rd t a_14 (&1:int)
     ==> valid_rd t a_15 (&1:int)
     ==> is_uint8 x_2
     ==> valid_rd t a_17 l_size
     ==> valid_rw t a_9 l_size
     ==> valid_rd t a_18 l_size
     ==> separated a_9 l_size a_18 l_size
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < l_size
            ==> separated a_17 l_size
                  (shift
                    (t_3 (shift (shift a i_2) (&0:int)))
                    (&0:int))
                  l_size)
     ==> (!i_2:int.
            let a_19 = shift a i_2 in
            (&0:int) <= i_2
            ==> i_2 < l_size
            ==> valid_rd t a_19 (&1:int) /\
                valid_rw t
                  (shift (t_3 (shift a_19 (&0:int))) (&0:int))
                  l_size)
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < l_size
            ==> (~(a_10 (shift a_16 i_2) = (&0:int)) <=>
                 ~(a_10 (shift a_8 i_2) = (&0:int))))
     ==> (!a_19:int#int.
            let a_20 = l_sched_group_cpus a_19 in
            let a_21 =
              shift (t_3 (shift a_20 (&0:int))) (&0:int) in
            valid_rd t a_20 (&1:int) /\
            valid_rd t a_21 l_size /\
            (!i_2:int.
               (&0:int) <= i_2
               ==> i_2 < l_size
               ==> separated a_21 l_size
                     (shift
                       (t_3 (shift (shift a i_2) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_19:int#int.
            let a_20 = l_sched_group_mask a_19 in
            let a_21 =
              shift (t_3 (shift a_20 (&0:int))) (&0:int) in
            valid_rd t a_20 (&1:int) /\
            valid_rd t a_21 l_size /\
            (!i_2:int.
               (&0:int) <= i_2
               ==> i_2 < l_size
               ==> separated a_21 l_size
                     (shift
                       (t_3 (shift (shift a i_2) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_19:int#int.
            let a_20 = l_group_balance_mask a_19 in
            let a_21 =
              shift (t_3 (shift a_20 (&0:int))) (&0:int) in
            valid_rd t a_20 (&1:int) /\
            valid_rd t a_21 l_size /\
            (!i_2:int.
               (&0:int) <= i_2
               ==> i_2 < l_size
               ==> separated a_21 l_size
                     (shift
                       (t_3 (shift (shift a i_2) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_2:int.
            let a_19 = l_cpu_smt_mask i_2 in
            let a_20 =
              shift (t_3 (shift a_19 (&0:int))) (&0:int) in
            (&0:int) <= i_2
            ==> i_2 < l_size
            ==> valid_rd t a_19 (&1:int) /\
                valid_rd t a_20 l_size /\
                (!i_3:int.
                   (&0:int) <= i_3
                   ==> i_3 < l_size
                   ==> separated a_20 l_size
                         (shift
                           (t_3
                             (shift (shift a i_3) (&0:int)))
                           (&0:int))
                         l_size))
     ==> ~(a_10 (shift a_8 i_1) = (&0:int))`;;
