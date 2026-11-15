(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_call_find_next_bit_pre_2_goal8:
  validity of reading a CPU SMT mask after the stated integer bounds, memory
  validity, framing, linking, idle-CPU, group-mask, and separation hypotheses.
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
   !i_2:int.
   !t_2:(int#int)->(int#int).
   !i i_1:int.
   !a:int#int.
   !t:int->int.
   !t_1:(int#int)->int.
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
     let a_1 = shift (l_cpu_smt_mask i_2) (&0:int) in
     let a_2 = t_2 a_1 in
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
     ==> ~(l_idle_cpu i_2 = (&0:int))
     ==> (&0:int) <= i
     ==> i < l_size
     ==> (&0:int) <= i_1
     ==> (&0:int) <= i_2
     ==> i_2 < l_size
     ==> i_1 <= l_size
     ==> region (FST a) <= (&0:int)
     ==> framed t_2
     ==> linked t
     ==> is_uint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> valid_rd t a_1 (&1:int)
     ==> (!i_3:int.
            ~(t_1 (shift a_2 i_3) = (&0:int))
            ==> (&0:int) <= i_3
            ==> i_3 < i_1
            ==> ~(l_idle_cpu i_3 = (&0:int)))
     ==> (!i_3:int.
            let a_3 = shift a i_3 in
            (&0:int) <= i_3
            ==> i_3 < l_size
            ==> valid_rd t a_3 (&1:int) /\
                valid_rw t
                  (shift (t_2 (shift a_3 (&0:int))) (&0:int))
                  l_size)
     ==> (!a_3:int#int.
            let a_4 = l_sched_group_cpus a_3 in
            let a_5 =
              shift (t_2 (shift a_4 (&0:int))) (&0:int) in
            valid_rd t a_4 (&1:int) /\
            valid_rd t a_5 l_size /\
            (!i_3:int.
               (&0:int) <= i_3
               ==> i_3 < l_size
               ==> separated a_5 l_size
                     (shift
                       (t_2
                         (shift (shift a i_3) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_3:int#int.
            let a_4 = l_sched_group_mask a_3 in
            let a_5 =
              shift (t_2 (shift a_4 (&0:int))) (&0:int) in
            valid_rd t a_4 (&1:int) /\
            valid_rd t a_5 l_size /\
            (!i_3:int.
               (&0:int) <= i_3
               ==> i_3 < l_size
               ==> separated a_5 l_size
                     (shift
                       (t_2
                         (shift (shift a i_3) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_3:int#int.
            let a_4 = l_group_balance_mask a_3 in
            let a_5 =
              shift (t_2 (shift a_4 (&0:int))) (&0:int) in
            valid_rd t a_4 (&1:int) /\
            valid_rd t a_5 l_size /\
            (!i_3:int.
               (&0:int) <= i_3
               ==> i_3 < l_size
               ==> separated a_5 l_size
                     (shift
                       (t_2
                         (shift (shift a i_3) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_3:int.
            let a_3 = l_cpu_smt_mask i_3 in
            let a_4 =
              shift (t_2 (shift a_3 (&0:int))) (&0:int) in
            (&0:int) <= i_3
            ==> i_3 < l_size
            ==> valid_rd t a_3 (&1:int) /\
                valid_rd t a_4 l_size /\
                (!i_4:int.
                   (&0:int) <= i_4
                   ==> i_4 < l_size
                   ==> separated a_4 l_size
                         (shift
                           (t_2
                             (shift (shift a i_4) (&0:int)))
                           (&0:int))
                         l_size))
     ==> valid_rd t (shift a_2 (&0:int)) l_size`;;
