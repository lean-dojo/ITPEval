(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_signed_overflow_goal27:
  a scheduler load-balancing verification condition asserting that the
  branch-selected signed 32-bit index is at most 2147483646, under the stated
  integer bounds, memory-validity, framing, separation, CPU-mask, and search
  assumptions. This file contains no proof.
*)

let statement =
  `!i_4:int.
   !region:int->int.
   !linked:(int->int)->bool.
   !l_size:int.
   !l_idle_cpu:int->int.
   !l_sched_group_cpus:(int#int)->(int#int).
   !l_sched_group_mask:(int#int)->(int#int).
   !l_group_balance_mask:(int#int)->(int#int).
   !l_cpu_smt_mask:int->(int#int).
   !a_1:int#int.
   !t_3:(int#int)->int.
   !t_5:(int#int)->(int#int).
   !a:int#int.
   !i:int.
   !a_2:int#int.
   !t_4:(int#int)->int.
   !t_1 t_2:(int#int)->int.
   !i_1 i_5 i_2:int.
   !t:int->int.
   !i_3:int.
   !p_1 p:bool.
     let shift =
       \(q:int#int) (k:int). (FST q,SND q + k) in
     let valid_rw =
       \(malloc:int->int) (q:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST q /\
             (&0:int) <= SND q /\
             SND q + n <= malloc (FST q) in
     let valid_rd =
       \(malloc:int->int) (q:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST q) /\
             (&0:int) <= SND q /\
             SND q + n <= malloc (FST q) in
     let separated =
       \(q:int#int) (n:int) (r:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST q = FST r) \/
         SND r + m <= SND q \/
         SND q + n <= SND r in
     let framed =
       \(mptr:(int#int)->(int#int)).
         !q:int#int. region (FST (mptr q)) <= (&0:int) in
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
        (q:int#int) (n:int) (r:int#int).
         if separated r (&1:int) q n then m1 r else m0 r in
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
     let x = l_idle_cpu i_4 in
     let a_3 = shift a_1 (&3:int) in
     let x_1 = t_3 a_3 in
     let a_4 = shift a_1 (&4:int) in
     let a_5 = t_5 a_4 in
     let a_6 = shift a_5 (&0:int) in
     let a_7 = t_5 a_6 in
     let a_8 = shift a_1 (&1:int) in
     let x_2 = t_3 a_8 in
     let x_3 = t_3 (shift a_7 x_2) in
     let a_9 = shift a_1 (&0:int) in
     let a_10 = shift a i in
     let a_11 = t_5 a_9 in
     let a_12 = shift a_11 (&1:int) in
     let a_13 = shift a_2 (&0:int) in
     let a_14 = shift (t_5 a_13) (&1:int) in
     let x_4 = t_4 a_14 in
     let a_15 = shift a_10 (&0:int) in
     let a_16 = shift a_11 (&0:int) in
     let a_17 = t_5 a_16 in
     let a_18 = l_group_balance_mask a_17 in
     let a_19 = t_5 a_15 in
     let a_20 = shift a_19 (&0:int) in
     let a_21 = shift a_7 (&0:int) in
     let a_22 = havoc t_1 t_3 a_20 l_size in
     let a_23 = t_5 (shift a_18 (&0:int)) in
     let a_24 = havoc t_2 t_3 a_20 l_size in
     let a_25 = a_24 (shift a_19 i_4) in
     let a_26 = a_24 (shift a_7 i_1) in
     let a_27 = a_24 (shift a_7 i_4) in
     let a_28 = a_24 (shift a_23 i_1) in
     let a_29 = a_24 a_12 in
     let a_30 = shift a_23 (&0:int) in
     let x_5 = to_uint32 i_5 in
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
     ==> (~(x = (&0:int)) <=> ~(i_2 = (&0:int)))
     ==> ~(x_1 = (&2:int))
     ==> ~(x_3 = (&0:int))
     ==> (&0:int) <= i
     ==> i < l_size
     ==> (&0:int) <= i_4
     ==> i_4 < l_size
     ==> (&0:int) <= i_5
     ==> i_5 <= l_size
     ==> to_uint32 i_4 < l_size
     ==> (&0:int) <= x_2
     ==> x_2 < l_size
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> framed t_5
     ==> linked t
     ==> is_uint8 i_2
     ==> is_uint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_3
     ==> is_sint32 i_4
     ==> is_sint32 i_5
     ==> valid_rd t a_1 (&5:int)
     ==> is_uint32 x_1
     ==> is_sint32 x_2
     ==> valid_rd t a_4 (&1:int)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_9 (&1:int)
     ==> valid_rd t a_10 (&1:int)
     ==> valid_rd t a_5 (&1:int)
     ==> valid_rd t (t_5 (shift a_1 (&2:int))) (&2:int)
     ==> valid_rd t a_11 (&2:int)
     ==> is_sint32 (t_3 a_12)
     ==> is_sint32 x_4
     ==> valid_rd t a_15 (&1:int)
     ==> valid_rd t a_6 (&1:int)
     ==> valid_rd t a_16 (&1:int)
     ==> valid_rd t a_17 (&1:int)
     ==> valid_rd t a_18 (&1:int)
     ==> is_uint8 x_3
     ==> valid_rd t a_20 l_size
     ==> valid_rd t a_21 l_size
     ==> valid_rw t a_20 l_size
     ==> is_uint8 (a_22 (shift a_7 (--(&1:int))))
     ==> is_uint8 (a_22 (shift a_23 (--(&1:int))))
     ==> is_uint8 a_25
     ==> is_uint8 a_26
     ==> is_uint8 a_27
     ==> is_uint8 a_28
     ==> is_sint32 (a_22 a_12)
     ==> is_sint32 a_29
     ==> valid_rd t a_30 l_size
     ==> separated a_20 l_size a_30 l_size
     ==> (if i_2 = (&0:int)
          then ~p_1 /\ i_4 = i_3
          else ~p /\
               p_1 /\
               a_2 = a_1 /\
               ~(x = (&0:int)) /\
               bit_and_7 x_4 = (&0:int) /\
               a_24 = t_4 /\
               ~(p_idle_core t_5 t_4 i_4) /\
               valid_rd t a_13 (&1:int) /\
               valid_rd t a_14 (&1:int))
     ==> (~(bit_and_7 a_29 = (&0:int))
          ==> i_1 = --(&1:int))
     ==> (~(i_1 = --(&1:int))
          ==> ~(l_idle_cpu i_1 = (&0:int)) /\
              ~(a_26 = (&0:int)) /\
              ~(a_28 = (&0:int)) /\
              (&0:int) <= i_1 /\
              i_1 < l_size)
     ==> (i_1 = --(&1:int)
          ==> (!i_6:int.
                 ~(a_24 (shift a_23 i_6) = (&0:int))
                 ==> (&0:int) <= i_6
                 ==> i_6 < l_size
                 ==> ~(a_24 (shift a_19 i_6) = (&0:int))))
     ==> ((?i_6:int.
             ~(a_24 (shift a_19 i_6) = (&0:int)) /\
             ~(a_24 (shift a_7 i_6) = (&0:int)) /\
             i_6 < l_size /\
             x_5 <= i_6)
          ==> x_5 <= i_4)
     ==> ((?i_6:int.
             ~(a_24 (shift a_19 i_6) = (&0:int)) /\
             ~(a_24 (shift a_7 i_6) = (&0:int)) /\
             i_6 < l_size /\
             x_5 <= i_6)
          ==> ~(a_25 = (&0:int)) /\
              ~(a_27 = (&0:int)))
     ==> ((!i_6:int.
             i_6 < l_size
             ==> x_5 <= i_6
             ==> a_24 (shift a_19 i_6) = (&0:int) \/
                 a_24 (shift a_7 i_6) = (&0:int))
          ==> l_size = i_4)
     ==> (~(i_1 = --(&1:int))
          ==> (!i_6:int.
                 ~(a_24 (shift a_7 i_6) = (&0:int))
                 ==> ~(a_24 (shift a_23 i_6) = (&0:int))
                 ==> (&0:int) <= i_6
                 ==> i_6 < i_1
                 ==> i_6 < l_size
                 ==> l_idle_cpu i_6 = (&0:int)))
     ==> (i_1 = --(&1:int)
          ==> (!i_6:int.
                 ~(a_24 (shift a_7 i_6) = (&0:int))
                 ==> ~(a_24 (shift a_23 i_6) = (&0:int))
                 ==> (&0:int) <= i_6
                 ==> i_6 < i_5
                 ==> i_6 < l_size
                 ==> l_idle_cpu i_6 = (&0:int)))
     ==> ((?i_6:int.
             ~(a_24 (shift a_19 i_6) = (&0:int)) /\
             ~(a_24 (shift a_7 i_6) = (&0:int)) /\
             i_6 < l_size /\
             x_5 <= i_6)
          ==> (!i_6:int.
                 i_6 < i_4
                 ==> x_5 <= i_6
                 ==> a_24 (shift a_19 i_6) = (&0:int) \/
                     a_24 (shift a_7 i_6) = (&0:int)))
     ==> (~(i_1 = --(&1:int))
          ==> (!i_6:int.
                 ~(a_24 (shift a_7 i_6) = (&0:int))
                 ==> ~(a_24 (shift a_23 i_6) = (&0:int))
                 ==> (&0:int) <= i_6
                 ==> i_1 <= i_6
                 ==> i_6 < i_5
                 ==> i_6 < l_size
                 ==> ~(p_idle_core t_5 a_24 i_6)))
     ==> (~(i_1 = --(&1:int))
          ==> (!i_6:int.
                 ~(a_24 (shift a_23 i_6) = (&0:int))
                 ==> (&0:int) <= i_6
                 ==> i_6 < l_size
                 ==> ~(a_24 (shift a_19 i_6) = (&0:int)) \/
                     ~(p_idle_core t_5 a_24 i_6)))
     ==> (i_2 = (&0:int) \/ i_2 = (&1:int))
     ==> (!i_6:int.
            (&0:int) <= i_6
            ==> i_6 < l_size
            ==> separated a_21 l_size
                  (shift
                    (t_5 (shift (shift a i_6) (&0:int)))
                    (&0:int))
                  l_size)
     ==> (!i_6:int.
            let a_31 = shift a i_6 in
            (&0:int) <= i_6
            ==> i_6 < l_size
            ==> valid_rd t a_31 (&1:int) /\
                valid_rw t
                  (shift (t_5 (shift a_31 (&0:int))) (&0:int))
                  l_size)
     ==> (!i_6:int.
            (&0:int) <= i_6
            ==> i_6 < l_size
            ==> (~(a_22 (shift a_23 i_6) = (&0:int)) <=>
                 ~(a_22 (shift a_19 i_6) = (&0:int))))
     ==> (!i_6:int.
            ~(a_24 (shift a_19 i_6) = (&0:int))
            ==> (&0:int) <= i_6
            ==> i_6 < l_size
            ==> ~(a_24 (shift a_23 i_6) = (&0:int)))
     ==> (!a_31:int#int.
            let a_32 = l_sched_group_cpus a_31 in
            let a_33 =
              shift (t_5 (shift a_32 (&0:int))) (&0:int) in
            valid_rd t a_32 (&1:int) /\
            valid_rd t a_33 l_size /\
            (!i_6:int.
               (&0:int) <= i_6
               ==> i_6 < l_size
               ==> separated a_33 l_size
                     (shift
                       (t_5 (shift (shift a i_6) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_31:int#int.
            let a_32 = l_sched_group_mask a_31 in
            let a_33 =
              shift (t_5 (shift a_32 (&0:int))) (&0:int) in
            valid_rd t a_32 (&1:int) /\
            valid_rd t a_33 l_size /\
            (!i_6:int.
               (&0:int) <= i_6
               ==> i_6 < l_size
               ==> separated a_33 l_size
                     (shift
                       (t_5 (shift (shift a i_6) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!a_31:int#int.
            let a_32 = l_group_balance_mask a_31 in
            let a_33 =
              shift (t_5 (shift a_32 (&0:int))) (&0:int) in
            valid_rd t a_32 (&1:int) /\
            valid_rd t a_33 l_size /\
            (!i_6:int.
               (&0:int) <= i_6
               ==> i_6 < l_size
               ==> separated a_33 l_size
                     (shift
                       (t_5 (shift (shift a i_6) (&0:int)))
                       (&0:int))
                     l_size))
     ==> (!i_6:int.
            let a_31 = l_cpu_smt_mask i_6 in
            let a_32 =
              shift (t_5 (shift a_31 (&0:int))) (&0:int) in
            (&0:int) <= i_6
            ==> i_6 < l_size
            ==> valid_rd t a_31 (&1:int) /\
                valid_rd t a_32 l_size /\
                (!i_7:int.
                   (&0:int) <= i_7
                   ==> i_7 < l_size
                   ==> separated a_32 l_size
                         (shift
                           (t_5
                             (shift (shift a i_7) (&0:int)))
                           (&0:int))
                         l_size))
     ==> (if p_1
          then i_4 <= (&2147483646:int)
          else i_3 <= (&2147483646:int))`;;
