;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_i5_preserved_goal21:
;; preservation of the non-idle-core loop invariant under integer bounds,
;; memory validity, framing, separation, havoc-memory agreement, and quantified
;; scheduling, CPU-mask layout, and mask reflexivity, symmetry, and transitivity
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb21-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb21-address-base (address)
  (car address))

(defun swb21-address-offset (address)
  (cdr address))

(defun swb21-shift (address amount)
  (cons
   (swb21-address-base address)
   (+ (swb21-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source integer memories t_1,
;; t_2, t_3, t_4, pointer memory t_5, allocation map t, and fixed symbols.

(defstub swb21-t1 (address) t)
(defstub swb21-t2 (address) t)
(defstub swb21-t3 (address) t)
(defstub swb21-t4 (address) t)
(defstub swb21-t5 (address) t)
(defstub swb21-allocation (index) t)
(defstub swb21-region (base) t)
(defstub swb21-linked-op () t)
(defstub swb21-l-size () t)
(defstub swb21-l-idle-cpu (index) t)
(defstub swb21-l-sched-group-cpus (address) t)
(defstub swb21-l-sched-group-mask (address) t)
(defstub swb21-l-group-balance-mask (address) t)
(defstub swb21-l-cpu-smt-mask (index) t)

;; Conservative evaluator schemas preserve the function arguments of the
;; imported Q_mask_refl, Q_mask_symm, and Q_mask_trans laws.

(defstub swb21-mask-memory-apply (memory-symbol address) t)
(defstub swb21-mask-pointer-apply (pointer-symbol address) t)

(defun swb21-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun swb21-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb21-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Preserve every source function type over the full unbounded integer and
;; address domains, together with the imported idle-CPU range property.

(defun-sk swb21-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb21-address-p address)
      (and
       (integerp (swb21-t1 address))
       (integerp (swb21-t2 address))
       (integerp (swb21-t3 address))
       (integerp (swb21-t4 address))
       (swb21-address-p (swb21-t5 address))
       (swb21-address-p
        (swb21-l-sched-group-cpus address))
       (swb21-address-p
        (swb21-l-sched-group-mask address))
       (swb21-address-p
        (swb21-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb21-allocation index))
       (swb21-is-uint8-p (swb21-l-idle-cpu index))
       (swb21-address-p (swb21-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb21-region base))))))

(defun-sk swb21-mask-schema-types-p ()
  (forall (memory-symbol pointer-symbol address)
    (implies
     (swb21-address-p address)
     (and
      (integerp
       (swb21-mask-memory-apply
        memory-symbol address))
      (swb21-address-p
       (swb21-mask-pointer-apply
        pointer-symbol address))))))

(defun-sk swb21-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb21-address-p address)
     (equal
      (swb21-mask-memory-apply
       'swb21-zero-memory address)
      0))))

;; Exact universal scopes of A_schedule_cpumask.Q_mask_refl,
;; A_schedule_cpumask.Q_mask_symm, and A_schedule_cpumask.Q_mask_trans.

(defun-sk swb21-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb21-l-size))
       (not
        (equal
         (swb21-mask-memory-apply
          memory-symbol
          (swb21-shift
           (swb21-mask-pointer-apply
            pointer-symbol
            (swb21-shift
             (swb21-l-cpu-smt-mask index)
             0))
           index))
         0)))))))

(defun-sk swb21-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and (integerp i) (integerp j))
     (implies
      (not
       (equal
        (swb21-mask-memory-apply
         memory-symbol
         (swb21-shift
          (swb21-mask-pointer-apply
           pointer-symbol
           (swb21-shift
            (swb21-l-cpu-smt-mask j)
            0))
          i))
        0))
      (implies
       (<= 0 i)
       (implies
        (< i (swb21-l-size))
        (implies
         (<= 0 j)
         (implies
          (< j (swb21-l-size))
          (not
           (equal
            (swb21-mask-memory-apply
             memory-symbol
             (swb21-shift
              (swb21-mask-pointer-apply
               pointer-symbol
               (swb21-shift
                (swb21-l-cpu-smt-mask i)
                0))
              j))
            0))))))))))

(defun-sk swb21-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and (integerp i) (integerp j) (integerp k))
     (implies
      (not
       (equal
        (swb21-mask-memory-apply
         memory-symbol
         (swb21-shift
          (swb21-mask-pointer-apply
           pointer-symbol
           (swb21-shift
            (swb21-l-cpu-smt-mask i)
            0))
          j))
        0))
      (implies
       (not
        (equal
         (swb21-mask-memory-apply
          memory-symbol
          (swb21-shift
           (swb21-mask-pointer-apply
            pointer-symbol
            (swb21-shift
             (swb21-l-cpu-smt-mask j)
             0))
           k))
         0))
       (implies
        (<= 0 i)
        (implies
         (< i (swb21-l-size))
         (implies
          (<= 0 j)
          (implies
           (< j (swb21-l-size))
           (implies
            (<= 0 k)
            (implies
             (< k (swb21-l-size))
             (not
              (equal
               (swb21-mask-memory-apply
                memory-symbol
                (swb21-shift
                 (swb21-mask-pointer-apply
                  pointer-symbol
                  (swb21-shift
                   (swb21-l-cpu-smt-mask i)
                   0))
                 k))
               0)))))))))))))

(defun swb21-linked-p ()
  (if (swb21-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun swb21-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swb21-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb21-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb21-address-base address))
    (<= 0 (swb21-address-offset address))
    (<=
     (+ (swb21-address-offset address) length)
     (swb21-allocation (swb21-address-base address))))))

(defun swb21-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb21-address-base address)))
    (<= 0 (swb21-address-offset address))
    (<=
     (+ (swb21-address-offset address) length)
     (swb21-allocation (swb21-address-base address))))))

(defun swb21-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb21-address-base left)
     (swb21-address-base right)))
   (<=
    (+ (swb21-address-offset right) right-length)
    (swb21-address-offset left))
   (<=
    (+ (swb21-address-offset left) left-length)
    (swb21-address-offset right))))

;; Exact unfolding of Memory.framed for t_5.

(defun-sk swb21-framed-p ()
  (forall (address)
    (implies
     (swb21-address-p address)
     (<=
      (swb21-region
       (swb21-address-base (swb21-t5 address)))
      0))))

;; Exact havoc_access values for a_12 = havoc t_2 t_3 and
;; a_21 = havoc t_1 t_3.

(defun swb21-havoc12-value
    (protected-start protected-length query)
  (if
      (swb21-separated-p
       query 1 protected-start protected-length)
      (swb21-t3 query)
    (swb21-t2 query)))

(defun swb21-havoc21-value
    (protected-start protected-length query)
  (if
      (swb21-separated-p
       query 1 protected-start protected-length)
      (swb21-t3 query)
    (swb21-t1 query)))

;; Extensional bridges select the VC-relevant instances of the generic mask
;; laws: mint_0 = a_12 and mptr_0 = t_5.

(defun-sk swb21-mask-havoc12-instance-p (protected-start)
  (forall (address)
    (implies
     (swb21-address-p address)
     (equal
      (swb21-mask-memory-apply
       'swb21-havoc12-memory
       address)
      (swb21-havoc12-value
       protected-start
       (swb21-l-size)
       address)))))

(defun-sk swb21-mask-t5-instance-p ()
  (forall (address)
    (implies
     (swb21-address-p address)
     (equal
      (swb21-mask-pointer-apply
       'swb21-t5-pointer
       address)
      (swb21-t5 address)))))

;; Exact function extensional equality a_12 = t_4 over every source address.

(defun-sk swb21-havoc12-equals-t4-p (protected-start)
  (forall (address)
    (implies
     (swb21-address-p address)
     (equal
      (swb21-havoc12-value
       protected-start
       (swb21-l-size)
       address)
      (swb21-t4 address)))))

;; Exact unfoldings of p_idle_core for t_4 and for the havoced memory a_12.

(defun-sk swb21-idle-core-t4-p (cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb21-t4
         (swb21-shift
          (swb21-t5
           (swb21-shift
            (swb21-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb21-l-size))
        (not
         (equal
          (swb21-l-idle-cpu index)
          0))))))))

(defun-sk swb21-idle-core-havoc12-p
    (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb21-havoc12-value
         protected-start
         (swb21-l-size)
         (swb21-shift
          (swb21-t5
           (swb21-shift
            (swb21-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb21-l-size))
        (not
         (equal
          (swb21-l-idle-cpu index)
          0))))))))

;; The existential paired-selection condition shared by three hypotheses.

(defun-sk swb21-selected-tail-exists-p
    (protected-start a10 a6 x4)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swb21-havoc12-value
        protected-start
        (swb21-l-size)
        (swb21-shift a10 index))
       0))
     (not
      (equal
       (swb21-havoc12-value
        protected-start
        (swb21-l-size)
        (swb21-shift a6 index))
       0))
     (< index (swb21-l-size))
     (<= x4 index))))

;; When i_1 is -1, every selected a_18 position maps to a selected a_10
;; position.

(defun-sk swb21-a18-to-a10-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb21-havoc12-value
         protected-start
         (swb21-l-size)
         (swb21-shift a18 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb21-l-size))
        (not
         (equal
          (swb21-havoc12-value
           protected-start
           (swb21-l-size)
           (swb21-shift a10 index))
          0))))))))

;; At every position from x_4 through l_size, at least one mask is zero.

(defun-sk swb21-tail-zero-p
    (protected-start a10 a6 x4)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index (swb21-l-size))
      (implies
       (<= x4 index)
       (or
        (equal
         (swb21-havoc12-value
          protected-start
          (swb21-l-size)
          (swb21-shift a10 index))
         0)
        (equal
         (swb21-havoc12-value
          protected-start
          (swb21-l-size)
          (swb21-shift a6 index))
         0)))))))

;; Every position selected by both a_6 and a_18 below a bound has idle value
;; zero.

(defun-sk swb21-selected-prefix-idle-zero-p
    (protected-start a6 a18 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb21-havoc12-value
         protected-start
         (swb21-l-size)
         (swb21-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb21-havoc12-value
          protected-start
          (swb21-l-size)
          (swb21-shift a18 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index bound)
         (implies
          (< index (swb21-l-size))
          (equal
           (swb21-l-idle-cpu index)
           0)))))))))

;; The paired-zero condition below i_6.

(defun-sk swb21-prefix-zero-p
    (protected-start a10 a6 x4 i6)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index i6)
      (implies
       (<= x4 index)
       (or
        (equal
         (swb21-havoc12-value
          protected-start
          (swb21-l-size)
          (swb21-shift a10 index))
         0)
        (equal
         (swb21-havoc12-value
          protected-start
          (swb21-l-size)
          (swb21-shift a6 index))
         0)))))))

;; Every position selected by both masks in [i_1, i_7) is not an idle core.

(defun-sk swb21-selected-range-not-idle-core-p
    (protected-start a6 a18 i1 i7)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb21-havoc12-value
         protected-start
         (swb21-l-size)
         (swb21-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb21-havoc12-value
          protected-start
          (swb21-l-size)
          (swb21-shift a18 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= i1 index)
         (implies
          (< index i7)
          (implies
           (< index (swb21-l-size))
           (not
            (swb21-idle-core-havoc12-p
             protected-start index)))))))))))

;; A selected a_18 position has either a selected a_10 position or is not an
;; idle core.

(defun-sk swb21-a18-to-a10-or-not-idle-core-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb21-havoc12-value
         protected-start
         (swb21-l-size)
         (swb21-shift a18 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb21-l-size))
        (or
         (not
          (equal
           (swb21-havoc12-value
            protected-start
            (swb21-l-size)
            (swb21-shift a10 index))
           0))
         (not
          (swb21-idle-core-havoc12-p
           protected-start index)))))))))

;; Separation of a_20 from every pointed-to CPU mask in the source array.

(defun-sk swb21-a20-separated-p (a20 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb21-l-size))
       (swb21-separated-p
        a20
        (swb21-l-size)
        (swb21-shift
         (swb21-t5
          (swb21-shift
           (swb21-shift a index)
           0))
         0)
        (swb21-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb21-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((a28 (swb21-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb21-l-size))
         (and
          (swb21-valid-rd-p a28 1)
          (swb21-valid-rw-p
           (swb21-shift
            (swb21-t5
             (swb21-shift a28 0))
            0)
           (swb21-l-size)))))))))

;; The two a_21 mask views agree at every valid array index.

(defun-sk swb21-havoc21-agreement-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb21-l-size))
       (iff
        (not
         (equal
          (swb21-havoc21-value
           protected-start
           (swb21-l-size)
           (swb21-shift a18 index))
          0))
        (not
         (equal
          (swb21-havoc21-value
           protected-start
           (swb21-l-size)
           (swb21-shift a10 index))
          0))))))))

;; Every selected a_10 position in a_12 is selected in a_18.

(defun-sk swb21-a10-to-a18-p
    (protected-start a10 a18)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb21-havoc12-value
         protected-start
         (swb21-l-size)
         (swb21-shift a10 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb21-l-size))
        (not
         (equal
          (swb21-havoc12-value
           protected-start
           (swb21-l-size)
           (swb21-shift a18 index))
          0))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb21-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb21-l-size))
       (swb21-separated-p
        mask
        (swb21-l-size)
        (swb21-shift
         (swb21-t5
          (swb21-shift
           (swb21-shift a index)
           0))
         0)
        (swb21-l-size)))))))

(defun-sk swb21-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb21-address-p address)
     (let*
         ((a29 (swb21-l-sched-group-cpus address))
          (a30
           (swb21-shift
            (swb21-t5
             (swb21-shift a29 0))
            0)))
       (and
        (swb21-valid-rd-p a29 1)
        (swb21-valid-rd-p a30 (swb21-l-size))
        (swb21-separated-from-array-masks-p a30 a))))))

(defun-sk swb21-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb21-address-p address)
     (let*
         ((a29 (swb21-l-sched-group-mask address))
          (a30
           (swb21-shift
            (swb21-t5
             (swb21-shift a29 0))
            0)))
       (and
        (swb21-valid-rd-p a29 1)
        (swb21-valid-rd-p a30 (swb21-l-size))
        (swb21-separated-from-array-masks-p a30 a))))))

(defun-sk swb21-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb21-address-p address)
     (let*
         ((a29 (swb21-l-group-balance-mask address))
          (a30
           (swb21-shift
            (swb21-t5
             (swb21-shift a29 0))
            0)))
       (and
        (swb21-valid-rd-p a29 1)
        (swb21-valid-rd-p a30 (swb21-l-size))
        (swb21-separated-from-array-masks-p a30 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb21-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((a28 (swb21-l-cpu-smt-mask index))
          (a29
           (swb21-shift
            (swb21-t5
             (swb21-shift a28 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb21-l-size))
         (and
          (swb21-valid-rd-p a28 1)
          (swb21-valid-rd-p a29 (swb21-l-size))
          (swb21-separated-from-array-masks-p a29 a))))))))

(defun swb21-goal-body
    (i6 a1 a i i1 i7 i3 i4 i5 i2 p)
  (implies
   (and
    (swb21-function-types-p)
    (swb21-mask-schema-types-p)
    (swb21-zero-mask-memory-instance-p)
    (swb21-q-mask-refl-p)
    (swb21-q-mask-symm-p)
    (swb21-q-mask-trans-p)
    (swb21-mask-t5-instance-p)
    (integerp (swb21-l-size))
    (< 0 (swb21-l-size))
    (<= (swb21-l-size) 2147483647)
    (swb21-address-p a1)
    (swb21-address-p a)
    (integerp i6)
    (integerp i)
    (integerp i1)
    (integerp i7)
    (integerp i3)
    (integerp i4)
    (integerp i5)
    (integerp i2)
    (booleanp p))
   (let*
       ((x (swb21-l-idle-cpu i6))
        (a2 (swb21-shift a1 3))
        (x1 (swb21-t3 a2))
        (a3 (swb21-shift a1 4))
        (a4 (swb21-t5 a3))
        (a5 (swb21-shift a4 0))
        (a6 (swb21-t5 a5))
        (a7 (swb21-shift a1 1))
        (x2 (swb21-t3 a7))
        (x3 (swb21-t3 (swb21-shift a6 x2)))
        (a8 (swb21-shift a i))
        (a9 (swb21-shift a8 0))
        (a10 (swb21-t5 a9))
        (a11 (swb21-shift a10 0))
        (a13 (swb21-shift a1 0))
        (a14 (swb21-t5 a13))
        (a15 (swb21-shift a14 0))
        (a16 (swb21-t5 a15))
        (a17 (swb21-l-group-balance-mask a16))
        (a18
         (swb21-t5
          (swb21-shift a17 0)))
        (a19 (swb21-shift a14 1))
        (a20 (swb21-shift a6 0))
        (a22
         (swb21-havoc12-value
          a11
          (swb21-l-size)
          (swb21-shift a10 i6)))
        (a23
         (swb21-havoc12-value
          a11
          (swb21-l-size)
          (swb21-shift a6 i1)))
        (a24
         (swb21-havoc12-value
          a11
          (swb21-l-size)
          (swb21-shift a6 i6)))
        (a25
         (swb21-havoc12-value
          a11
          (swb21-l-size)
          (swb21-shift a18 i1)))
        (a26
         (swb21-havoc12-value
          a11
          (swb21-l-size)
          a19))
        (a27 (swb21-shift a18 0))
        (x4 (swb21-to-uint32 i7)))
     (implies
     (and
       (swb21-mask-havoc12-instance-p a11)
       (not (equal i3 -1))
       (iff
        (not (equal x 0))
        (not (equal i4 0)))
       (not (equal x1 2))
       (not (equal x3 0))
       (not
        (equal
         (swb21-havoc12-value
          a11
          (swb21-l-size)
          (swb21-shift a6 i5))
         0))
       (not
        (equal
         (swb21-havoc12-value
          a11
          (swb21-l-size)
          (swb21-shift a18 i5))
         0))
       (<= 0 i)
       (< i (swb21-l-size))
       (<= 0 i5)
       (<= i3 i5)
       (< i5 (swb21-l-size))
       (<= 0 i6)
       (<= i5 i6)
       (< i6 (swb21-l-size))
       (<= 0 i7)
       (<= i7 (swb21-l-size))
       (< (swb21-to-uint32 i6) (swb21-l-size))
       (<= 0 x2)
       (< x2 (swb21-l-size))
       (<= (swb21-region (swb21-address-base a)) 0)
       (<= (swb21-region (swb21-address-base a1)) 0)
       (swb21-framed-p)
       (swb21-linked-p)
       (swb21-is-uint8-p i4)
       (swb21-is-uint32-p i)
       (swb21-is-sint32-p i1)
       (swb21-is-sint32-p i2)
       (swb21-is-sint32-p i3)
       (swb21-is-sint32-p i6)
       (swb21-is-sint32-p i7)
       (swb21-valid-rd-p a1 5)
       (swb21-is-uint32-p x1)
       (swb21-is-sint32-p (+ 1 i6))
       (swb21-is-sint32-p x2)
       (swb21-valid-rd-p a3 1)
       (swb21-valid-rd-p a7 1)
       (swb21-valid-rd-p a2 1)
       (swb21-valid-rd-p a13 1)
       (swb21-valid-rd-p a8 1)
       (swb21-valid-rd-p a4 1)
       (swb21-valid-rd-p
        (swb21-t5 (swb21-shift a1 2))
        2)
       (swb21-valid-rd-p a14 2)
       (swb21-is-sint32-p (swb21-t3 a19))
       (swb21-valid-rd-p a9 1)
       (swb21-valid-rd-p a5 1)
       (swb21-valid-rd-p a15 1)
       (swb21-valid-rd-p a16 1)
       (swb21-valid-rd-p a17 1)
       (swb21-is-uint8-p x3)
       (swb21-valid-rd-p a11 (swb21-l-size))
       (swb21-valid-rd-p a20 (swb21-l-size))
       (swb21-valid-rw-p a11 (swb21-l-size))
       (swb21-is-uint8-p
        (swb21-havoc21-value
         a11
         (swb21-l-size)
         (swb21-shift a6 -1)))
       (swb21-is-uint8-p
        (swb21-havoc21-value
         a11
         (swb21-l-size)
         (swb21-shift a18 -1)))
       (swb21-is-uint8-p a22)
       (swb21-is-uint8-p a23)
       (swb21-is-uint8-p
        (swb21-havoc12-value
         a11
         (swb21-l-size)
         (swb21-shift a6 i3)))
       (swb21-is-uint8-p a24)
       (swb21-is-uint8-p a25)
       (swb21-is-uint8-p
        (swb21-havoc12-value
         a11
         (swb21-l-size)
         (swb21-shift a18 i3)))
       (swb21-is-sint32-p
        (swb21-havoc21-value
         a11
         (swb21-l-size)
         a19))
       (swb21-is-sint32-p a26)
       (swb21-valid-rd-p a27 (swb21-l-size))
       (swb21-separated-p
        a11
        (swb21-l-size)
        a27
        (swb21-l-size))
       (if
           (equal i4 0)
           (and
            (equal i3 i1)
            (<= i6 2147483646))
         (and
          (equal p nil)
          (equal i2 i1)
          (not (equal x 0))
          (equal
           (swb21-land 7 (swb21-t4 a19))
           0)
          (swb21-havoc12-equals-t4-p a11)
          (<= i6 2147483646)
          (not (swb21-idle-core-t4-p i6))
          (swb21-valid-rd-p a19 1)
          (if
              (equal i2 -1)
              (equal i6 i3)
            (equal i3 i2))))
       (implies
        (not
         (equal
          (swb21-land 7 a26)
          0))
        (equal i1 -1))
       (implies
        (not (equal i1 -1))
        (and
         (not (equal (swb21-l-idle-cpu i1) 0))
         (not (equal a23 0))
         (not (equal a25 0))
         (<= 0 i1)
         (< i1 (swb21-l-size))))
       (implies
        (equal i1 -1)
        (swb21-a18-to-a10-p a11 a18 a10))
       (implies
        (swb21-selected-tail-exists-p
         a11 a10 a6 x4)
        (<= x4 i6))
       (implies
        (swb21-selected-tail-exists-p
         a11 a10 a6 x4)
        (and
         (not (equal a22 0))
         (not (equal a24 0))))
       (implies
        (swb21-tail-zero-p a11 a10 a6 x4)
        (equal (swb21-l-size) i6))
       (implies
        (not (equal i1 -1))
        (swb21-selected-prefix-idle-zero-p
         a11 a6 a18 i1))
       (implies
        (equal i1 -1)
        (swb21-selected-prefix-idle-zero-p
         a11 a6 a18 i7))
       (implies
        (swb21-selected-tail-exists-p
         a11 a10 a6 x4)
        (swb21-prefix-zero-p
         a11 a10 a6 x4 i6))
       (implies
        (not (equal i1 -1))
        (swb21-selected-range-not-idle-core-p
         a11 a6 a18 i1 i7))
       (implies
        (not (equal i1 -1))
        (swb21-a18-to-a10-or-not-idle-core-p
         a11 a18 a10))
       (or (equal i4 0) (equal i4 1))
       (swb21-a20-separated-p a20 a)
       (swb21-array-layout-p a)
       (swb21-havoc21-agreement-p a11 a18 a10)
       (swb21-a10-to-a18-p a11 a10 a18)
       (swb21-sched-group-cpus-layout-p a)
       (swb21-sched-group-mask-layout-p a)
       (swb21-group-balance-mask-layout-p a)
       (swb21-cpu-smt-layout-p a))
      (not
       (swb21-idle-core-havoc12-p
        a11 i5))))))

(defun-sk
    ntp4vc-should-we-balance-loop-inv-i5-preserved-goal21-statement ()
  (forall
   (i6 a1 a i i1 i7 i3 i4 i5 i2 p)
   (swb21-goal-body
    i6 a1 a i i1 i7 i3 i4 i5 i2 p)))

(value-triple :itpeval-statement-checked)

:q
