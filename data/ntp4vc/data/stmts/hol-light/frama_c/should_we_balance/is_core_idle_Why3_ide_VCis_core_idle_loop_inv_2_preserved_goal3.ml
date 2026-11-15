(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_loop_inv_2_preserved_goal3:
  preservation of the idle-core loop invariant under the stated CPU-mask,
  integer-range, memory-validity, framing, layout, separation, and quantified
  search hypotheses. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_size:int.
   !l_idle_cpu:int->int.
   !l_sched_group_cpus:(int#int)->(int#int).
   !l_sched_group_mask:(int#int)->(int#int).
   !l_group_balance_mask:(int#int)->(int#int).
   !l_cpu_smt_mask:int->(int#int).
   !i_5:int.
   !t_2:(int#int)->(int#int).
   !t_1:(int#int)->int.
   !i_4 i_2 i_3 i i_1:int.
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
     let a_1 = shift (l_cpu_smt_mask i_5) (&0:int) in
     let a_2 = t_2 a_1 in
     let x = t_1 (shift a_2 i_4) in
     let x_1 = to_uint32 i_2 in
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
     ==> (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> ~(l_idle_cpu i_5 = (&0:int))
     ==> ~(t_1 (shift a_2 i_3) = (&0:int))
     ==> (&0:int) <= i
     ==> i < l_size
     ==> i_3 <= i_1
     ==> (&0:int) <= i_2
     ==> (&0:int) <= i_3
     ==> (&0:int) <= i_5
     ==> i_5 < l_size
     ==> i_2 <= l_size
     ==> to_uint32 i_4 < l_size
     ==> region (FST a) <= (&0:int)
     ==> framed t_2
     ==> linked t
     ==> is_uint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> is_sint32 i_4
     ==> is_sint32 i_5
     ==> is_sint32 ((&1:int) + i_1)
     ==> valid_rd t a_1 (&1:int)
     ==> is_uint8 x
     ==> valid_rd t (shift a_2 (&0:int)) l_size
     ==> (if i_5 = i_4
          then i_5 = i_1 /\ i_5 <= (&2147483646:int)
          else i_4 = i_1 /\
               ~(l_idle_cpu i_4 = (&0:int)) /\
               (&0:int) <= i_4 /\
               i_4 < l_size /\
               i_4 <= (&2147483646:int))
     ==> ((!i_6:int.
             i_6 < l_size
             ==> x_1 <= i_6
             ==> t_1 (shift a_2 i_6) = (&0:int))
          ==> l_size = i_4)
     ==> ((?i_6:int.
             ~(t_1 (shift a_2 i_6) = (&0:int)) /\
             i_6 < l_size /\
             x_1 <= i_6)
          ==> ~(x = (&0:int)))
     ==> ((?i_6:int.
             ~(t_1 (shift a_2 i_6) = (&0:int)) /\
             i_6 < l_size /\
             x_1 <= i_6)
          ==> i_4 < l_size)
     ==> ((?i_6:int.
             ~(t_1 (shift a_2 i_6) = (&0:int)) /\
             i_6 < l_size /\
             x_1 <= i_6)
          ==> i_4 < l_size /\ x_1 <= i_4)
     ==> ((?i_6:int.
             ~(t_1 (shift a_2 i_6) = (&0:int)) /\
             i_6 < l_size /\
             x_1 <= i_6)
          ==> (!i_6:int.
                 i_6 < i_4
                 ==> x_1 <= i_6
                 ==> t_1 (shift a_2 i_6) = (&0:int)))
     ==> (!i_6:int.
            ~(t_1 (shift a_2 i_6) = (&0:int))
            ==> (&0:int) <= i_6
            ==> i_6 < i_2
            ==> ~(l_idle_cpu i_6 = (&0:int)))
     ==> (!i_6:int.
            let a_3 = shift a i_6 in
            (&0:int) <= i_6
            ==> i_6 < l_size
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
            (!i_6:int.
               (&0:int) <= i_6
               ==> i_6 < l_size
               ==> separated a_5 l_size
                     (shift
                       (t_2
                         (shift (shift a i_6) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_3:int#int.
            let a_4 = l_sched_group_mask a_3 in
            let a_5 =
              shift (t_2 (shift a_4 (&0:int))) (&0:int) in
            valid_rd t a_4 (&1:int) /\
            valid_rd t a_5 l_size /\
            (!i_6:int.
               (&0:int) <= i_6
               ==> i_6 < l_size
               ==> separated a_5 l_size
                     (shift
                       (t_2
                         (shift (shift a i_6) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_3:int#int.
            let a_4 = l_group_balance_mask a_3 in
            let a_5 =
              shift (t_2 (shift a_4 (&0:int))) (&0:int) in
            valid_rd t a_4 (&1:int) /\
            valid_rd t a_5 l_size /\
            (!i_6:int.
               (&0:int) <= i_6
               ==> i_6 < l_size
               ==> separated a_5 l_size
                     (shift
                       (t_2
                         (shift (shift a i_6) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_6:int.
            let a_3 = l_cpu_smt_mask i_6 in
            let a_4 =
              shift (t_2 (shift a_3 (&0:int))) (&0:int) in
            (&0:int) <= i_6
            ==> i_6 < l_size
            ==> valid_rd t a_3 (&1:int) /\
                valid_rd t a_4 l_size /\
                (!i_7:int.
                   (&0:int) <= i_7
                   ==> i_7 < l_size
                   ==> separated a_4 l_size
                         (shift
                           (t_2
                             (shift (shift a i_7) (&0:int)))
                           (&0:int))
                         l_size))
     ==> ~(l_idle_cpu i_3 = (&0:int))`;;
