(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_complete_not_newly_idle_without_idle_no____goal0:
  the complete should-we-balance case split for newly idle and non-idle CPUs,
  under the stated integer bounds, memory validity, framing, separation, and
  CPU-mask layout hypotheses. This file contains no proof.
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
   !t_1:(int#int)->int.
   !a_1:int#int.
   !t_2:(int#int)->(int#int).
   !i:int.
   !a:int#int.
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
     let bit_and_7 =
       \z:int. z rem (&8:int) in
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
     let x = t_1 (shift a_1 (&1:int)) in
     let x_1 = t_1 (shift a_1 (&3:int)) in
     let a_2 = t_2 (shift a_1 (&4:int)) in
     let a_3 = t_2 (shift a_1 (&0:int)) in
     let x_2 = t_1 (shift a_3 (&1:int)) in
     let a_4 = t_2 (shift a_3 (&0:int)) in
     let a_5 = t_2 (shift a_2 (&0:int)) in
     let x_3 = t_1 (shift a_5 x) in
     let a_6 = shift a_5 (&0:int) in
     let a_7 =
       t_2 (shift (l_group_balance_mask a_4) (&0:int)) in
     let x_4 = bit_and_7 x_2 in
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
     ==> (&0:int) <= i
     ==> i < l_size
     ==> (&0:int) <= x
     ==> x < l_size
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> framed t_2
     ==> linked t
     ==> is_uint32 i
     ==> valid_rd t a_1 (&5:int)
     ==> is_uint32 x_1
     ==> is_sint32 x
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t (t_2 (shift a_1 (&2:int))) (&2:int)
     ==> valid_rd t a_3 (&2:int)
     ==> is_sint32 x_2
     ==> valid_rd t a_4 (&1:int)
     ==> is_uint8 x_3
     ==> valid_rd t a_6 l_size
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 < l_size
            ==> separated a_6 l_size
                  (shift
                    (t_2 (shift (shift a i_1) (&0:int)))
                    (&0:int))
                  l_size)
     ==> (!i_1:int.
            let a_8 = shift a i_1 in
            (&0:int) <= i_1
            ==> i_1 < l_size
            ==> valid_rd t a_8 (&1:int) /\
                valid_rw t
                  (shift (t_2 (shift a_8 (&0:int))) (&0:int))
                  l_size)
     ==> (!a_8:int#int.
            let a_9 = l_sched_group_cpus a_8 in
            let a_10 =
              shift (t_2 (shift a_9 (&0:int))) (&0:int) in
            valid_rd t a_9 (&1:int) /\
            valid_rd t a_10 l_size /\
            (!i_1:int.
               (&0:int) <= i_1
               ==> i_1 < l_size
               ==> separated a_10 l_size
                     (shift
                       (t_2 (shift (shift a i_1) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_8:int#int.
            let a_9 = l_sched_group_mask a_8 in
            let a_10 =
              shift (t_2 (shift a_9 (&0:int))) (&0:int) in
            valid_rd t a_9 (&1:int) /\
            valid_rd t a_10 l_size /\
            (!i_1:int.
               (&0:int) <= i_1
               ==> i_1 < l_size
               ==> separated a_10 l_size
                     (shift
                       (t_2 (shift (shift a i_1) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_8:int#int.
            let a_9 = l_group_balance_mask a_8 in
            let a_10 =
              shift (t_2 (shift a_9 (&0:int))) (&0:int) in
            valid_rd t a_9 (&1:int) /\
            valid_rd t a_10 l_size /\
            (!i_1:int.
               (&0:int) <= i_1
               ==> i_1 < l_size
               ==> separated a_10 l_size
                     (shift
                       (t_2 (shift (shift a i_1) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_1:int.
            let a_8 = l_cpu_smt_mask i_1 in
            let a_9 =
              shift (t_2 (shift a_8 (&0:int))) (&0:int) in
            (&0:int) <= i_1
            ==> i_1 < l_size
            ==> valid_rd t a_8 (&1:int) /\
                valid_rd t a_9 l_size /\
                (!i_2:int.
                   (&0:int) <= i_2
                   ==> i_2 < l_size
                   ==> separated a_9 l_size
                         (shift
                           (t_2
                             (shift (shift a i_2) (&0:int)))
                           (&0:int))
                         l_size))
     ==> (x_3 = (&0:int) \/
          (x_1 = (&2:int) /\ ~(x_3 = (&0:int))) \/
          (~(x_1 = (&2:int)) /\
           ~(x_3 = (&0:int)) /\
           (!i_1:int.
              ~(t_1 (shift a_5 i_1) = (&0:int))
              ==> ~(t_1 (shift a_7 i_1) = (&0:int))
              ==> (&0:int) <= i_1
              ==> i_1 < l_size
              ==> l_idle_cpu i_1 = (&0:int))) \/
          (~(x_1 = (&2:int)) /\
           x_4 = (&0:int) /\
           ~(x_3 = (&0:int)) /\
           (?i_1:int.
              ~(t_1 (shift a_5 i_1) = (&0:int)) /\
              ~(t_1 (shift a_7 i_1) = (&0:int)) /\
              (&0:int) <= i_1 /\
              i_1 < l_size /\
              p_idle_core t_2 t_1 i_1)) \/
          (~(x_1 = (&2:int)) /\
           ~(x_4 = (&0:int)) /\
           ~(x_3 = (&0:int)) /\
           (?i_1:int.
              ~(l_idle_cpu i_1 = (&0:int)) /\
              ~(t_1 (shift a_5 i_1) = (&0:int)) /\
              ~(t_1 (shift a_7 i_1) = (&0:int)) /\
              (&0:int) <= i_1 /\
              i_1 < l_size)) \/
          (~(x_1 = (&2:int)) /\
           x_4 = (&0:int) /\
           ~(x_3 = (&0:int)) /\
           (!i_1:int.
              ~(t_1 (shift a_5 i_1) = (&0:int))
              ==> ~(t_1 (shift a_7 i_1) = (&0:int))
              ==> (&0:int) <= i_1
              ==> i_1 < l_size
              ==> ~(p_idle_core t_2 t_1 i_1)) /\
           (?i_1:int.
              ~(l_idle_cpu i_1 = (&0:int)) /\
              ~(t_1 (shift a_5 i_1) = (&0:int)) /\
              ~(t_1 (shift a_7 i_1) = (&0:int)) /\
              (&0:int) <= i_1 /\
              i_1 < l_size)))`;;
