;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_not_newly_idle_with_idle_cpu_post_2_goal39:
;; the should-we-balance postcondition for a non-newly-idle CPU when an idle
;; CPU is available, with integer bounds, memory validity, framing, separation,
;; havoc-memory agreement, quantified CPU-mask layouts, and universal mask
;; reflexivity, symmetry, and transitivity assumptions. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb39-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb39-address-base (address)
  (car address))

(defun swb39-address-offset (address)
  (cdr address))

(defun swb39-shift (address amount)
  (cons
   (swb39-address-base address)
   (+ (swb39-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memories, allocation
;; maps, and fixed symbols.

(defstub swb39-t7 (address) t)
(defstub swb39-t6 (address) t)
(defstub swb39-t5 (address) t)
(defstub swb39-t8 (address) t)

(defstub swb39-allocation-t (index) t)
(defstub swb39-allocation-t4 (index) t)
(defstub swb39-allocation-t1 (index) t)
(defstub swb39-allocation-t2 (index) t)
(defstub swb39-allocation-t3 (index) t)

(defstub swb39-region (base) t)
(defstub swb39-linked-op () t)
(defstub swb39-l-size () t)
(defstub swb39-l-idle-cpu (index) t)
(defstub swb39-l-sched-group-cpus (address) t)
(defstub swb39-l-sched-group-mask (address) t)
(defstub swb39-l-group-balance-mask (address) t)
(defstub swb39-l-group-balance-cpu (address) t)
(defstub swb39-l-cpu-smt-mask (index) t)

;; Conservative evaluator schemas preserve the function arguments of the
;; imported Q_mask_refl, Q_mask_symm, and Q_mask_trans laws.

(defstub swb39-mask-memory-apply (memory-symbol address) t)
(defstub swb39-mask-pointer-apply (pointer-symbol address) t)

(defun swb39-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun swb39-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb39-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Preserve every source function type over the full unbounded integer and
;; address domains, together with the imported idle-CPU range property.

(defun-sk swb39-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb39-address-p address)
      (and
       (integerp (swb39-t7 address))
       (integerp (swb39-t6 address))
       (integerp (swb39-t5 address))
       (swb39-address-p (swb39-t8 address))
       (swb39-address-p
        (swb39-l-sched-group-cpus address))
       (swb39-address-p
        (swb39-l-sched-group-mask address))
       (swb39-address-p
        (swb39-l-group-balance-mask address))
       (integerp
        (swb39-l-group-balance-cpu address))))
     (implies
      (integerp index)
      (and
       (integerp (swb39-allocation-t index))
       (integerp (swb39-allocation-t4 index))
       (integerp (swb39-allocation-t1 index))
       (integerp (swb39-allocation-t2 index))
       (integerp (swb39-allocation-t3 index))
       (swb39-is-uint8-p (swb39-l-idle-cpu index))
       (swb39-address-p (swb39-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb39-region base))))))

(defun-sk swb39-mask-schema-types-p ()
  (forall (memory-symbol pointer-symbol address)
    (implies
     (swb39-address-p address)
     (and
      (integerp
       (swb39-mask-memory-apply
        memory-symbol address))
      (swb39-address-p
       (swb39-mask-pointer-apply
        pointer-symbol address))))))

(defun-sk swb39-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb39-address-p address)
     (equal
      (swb39-mask-memory-apply
       'swb39-zero-memory address)
      0))))

;; Exact universal scopes of A_schedule_cpumask.Q_mask_refl,
;; A_schedule_cpumask.Q_mask_symm, and A_schedule_cpumask.Q_mask_trans.

(defun-sk swb39-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb39-l-size))
       (not
        (equal
         (swb39-mask-memory-apply
          memory-symbol
          (swb39-shift
           (swb39-mask-pointer-apply
            pointer-symbol
            (swb39-shift
             (swb39-l-cpu-smt-mask index)
             0))
           index))
         0)))))))

(defun-sk swb39-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and (integerp i) (integerp j))
     (implies
      (not
       (equal
        (swb39-mask-memory-apply
         memory-symbol
         (swb39-shift
          (swb39-mask-pointer-apply
           pointer-symbol
           (swb39-shift
            (swb39-l-cpu-smt-mask j)
            0))
          i))
        0))
      (implies
       (<= 0 i)
       (implies
        (< i (swb39-l-size))
        (implies
         (<= 0 j)
         (implies
          (< j (swb39-l-size))
          (not
           (equal
            (swb39-mask-memory-apply
             memory-symbol
             (swb39-shift
              (swb39-mask-pointer-apply
               pointer-symbol
               (swb39-shift
                (swb39-l-cpu-smt-mask i)
                0))
              j))
            0))))))))))

(defun-sk swb39-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and (integerp i) (integerp j) (integerp k))
     (implies
      (not
       (equal
        (swb39-mask-memory-apply
         memory-symbol
         (swb39-shift
          (swb39-mask-pointer-apply
           pointer-symbol
           (swb39-shift
            (swb39-l-cpu-smt-mask i)
            0))
          j))
        0))
      (implies
       (not
        (equal
         (swb39-mask-memory-apply
          memory-symbol
          (swb39-shift
           (swb39-mask-pointer-apply
            pointer-symbol
            (swb39-shift
             (swb39-l-cpu-smt-mask j)
             0))
           k))
         0))
       (implies
        (<= 0 i)
        (implies
         (< i (swb39-l-size))
         (implies
          (<= 0 j)
          (implies
           (< j (swb39-l-size))
           (implies
            (<= 0 k)
            (implies
             (< k (swb39-l-size))
             (not
              (equal
               (swb39-mask-memory-apply
                memory-symbol
                (swb39-shift
                 (swb39-mask-pointer-apply
                  pointer-symbol
                  (swb39-shift
                   (swb39-l-cpu-smt-mask i)
                   0))
                 k))
               0)))))))))))))

(defun swb39-linked-p ()
  (if (swb39-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32), and Cbits.land is
;; mathematical bitwise conjunction on integers.

(defun swb39-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun swb39-land (left right)
  (logand left right))

;; A finite selector is only a definitional abbreviation for the five named
;; source allocation maps.

(defun swb39-allocation-value (which index)
  (cond
   ((equal which :t4)
    (swb39-allocation-t4 index))
   ((equal which :t1)
    (swb39-allocation-t1 index))
   ((equal which :t2)
    (swb39-allocation-t2 index))
   ((equal which :t3)
    (swb39-allocation-t3 index))
   (t
    (swb39-allocation-t index))))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb39-valid-rw-p (which address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb39-address-base address))
    (<= 0 (swb39-address-offset address))
    (<=
     (+ (swb39-address-offset address) length)
     (swb39-allocation-value
      which
      (swb39-address-base address))))))

(defun swb39-valid-rd-p (which address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb39-address-base address)))
    (<= 0 (swb39-address-offset address))
    (<=
     (+ (swb39-address-offset address) length)
     (swb39-allocation-value
      which
      (swb39-address-base address))))))

(defun swb39-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb39-address-base left)
     (swb39-address-base right)))
   (<=
    (+ (swb39-address-offset right) right-length)
    (swb39-address-offset left))
   (<=
    (+ (swb39-address-offset left) left-length)
    (swb39-address-offset right))))

;; Exact function equality for the allocation maps appearing in the branch
;; conditions.

(defun-sk swb39-allocations-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (swb39-allocation-value left index)
      (swb39-allocation-value right index)))))

;; Exact unfolding of Memory.framed for t_8.

(defun-sk swb39-framed-p ()
  (forall (address)
    (implies
     (swb39-address-p address)
     (<=
      (swb39-region
       (swb39-address-base (swb39-t8 address)))
      0))))

;; Exact havoc_access values a_20 = havoc t_6 t_7 and
;; a_28 = havoc t_5 t_7.

(defun swb39-havoc6-value
    (protected-start protected-length query)
  (if
      (swb39-separated-p
       query 1 protected-start protected-length)
      (swb39-t7 query)
    (swb39-t6 query)))

(defun swb39-havoc5-value
    (protected-start protected-length query)
  (if
      (swb39-separated-p
       query 1 protected-start protected-length)
      (swb39-t7 query)
    (swb39-t5 query)))

;; Extensional bridges select every VC-relevant instance of the generic mask
;; laws: pointer memory t_8, integer memory t_7, and the two named havoc
;; memories a_20 and a_28.

(defun-sk swb39-mask-t8-instance-p ()
  (forall (address)
    (implies
     (swb39-address-p address)
     (equal
      (swb39-mask-pointer-apply
       'swb39-t8-pointer
       address)
      (swb39-t8 address)))))

(defun-sk swb39-mask-t7-instance-p ()
  (forall (address)
    (implies
     (swb39-address-p address)
     (equal
      (swb39-mask-memory-apply
       'swb39-t7-memory
       address)
      (swb39-t7 address)))))

(defun-sk swb39-mask-havoc6-instance-p
    (protected-start)
  (forall (address)
    (implies
     (swb39-address-p address)
     (equal
      (swb39-mask-memory-apply
       'swb39-havoc6-memory
       address)
      (swb39-havoc6-value
       protected-start
       (swb39-l-size)
       address)))))

(defun-sk swb39-mask-havoc5-instance-p
    (protected-start)
  (forall (address)
    (implies
     (swb39-address-p address)
     (equal
      (swb39-mask-memory-apply
       'swb39-havoc5-memory
       address)
      (swb39-havoc5-value
       protected-start
       (swb39-l-size)
       address)))))

;; Exact unfoldings of p_idle_core for the two memories used by this VC.

(defun-sk swb39-idle-core-havoc6-p
    (protected-start protected-length cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-havoc6-value
         protected-start
         protected-length
         (swb39-shift
          (swb39-t8
           (swb39-shift
            (swb39-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb39-l-size))
        (not
         (equal
          (swb39-l-idle-cpu index)
          0))))))))

(defun-sk swb39-idle-core-t7-p (cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-t7
         (swb39-shift
          (swb39-t8
           (swb39-shift
            (swb39-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb39-l-size))
        (not
         (equal
          (swb39-l-idle-cpu index)
          0))))))))

;; The existential paired-selection condition shared by several hypotheses.

(defun-sk swb39-selected-tail-exists-p
    (protected-start a17 a9 lower)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swb39-havoc6-value
        protected-start
        (swb39-l-size)
        (swb39-shift a17 index))
       0))
     (not
      (equal
       (swb39-havoc6-value
        protected-start
        (swb39-l-size)
        (swb39-shift a9 index))
       0))
     (< index (swb39-l-size))
     (<= lower index))))

;; Quantified selection and idle-core conditions from the loop invariants.

(defun-sk swb39-a14-selection-implies-a17-p
    (protected-start a14 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-havoc6-value
         protected-start
         (swb39-l-size)
         (swb39-shift a14 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb39-l-size))
        (not
         (equal
          (swb39-havoc6-value
           protected-start
           (swb39-l-size)
           (swb39-shift a17 index))
          0))))))))

(defun-sk swb39-no-selected-tail-p
    (protected-start a17 a9 lower)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index (swb39-l-size))
      (implies
       (<= lower index)
       (or
        (equal
         (swb39-havoc6-value
          protected-start
          (swb39-l-size)
          (swb39-shift a17 index))
         0)
        (equal
         (swb39-havoc6-value
          protected-start
          (swb39-l-size)
          (swb39-shift a9 index))
         0)))))))

(defun-sk swb39-no-selected-prefix-p
    (protected-start a17 a9 lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index upper)
      (implies
       (<= lower index)
       (or
        (equal
         (swb39-havoc6-value
          protected-start
          (swb39-l-size)
          (swb39-shift a17 index))
         0)
        (equal
         (swb39-havoc6-value
          protected-start
          (swb39-l-size)
          (swb39-shift a9 index))
         0)))))))

(defun-sk swb39-selected-prefix-idle-zero-p
    (protected-start a9 a14 upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-havoc6-value
         protected-start
         (swb39-l-size)
         (swb39-shift a9 index))
        0))
      (implies
       (not
        (equal
         (swb39-havoc6-value
          protected-start
          (swb39-l-size)
          (swb39-shift a14 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index upper)
         (implies
          (< index (swb39-l-size))
          (equal
           (swb39-l-idle-cpu index)
           0)))))))))

(defun-sk swb39-selected-range-not-idle-p
    (protected-start a9 a14 lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-havoc6-value
         protected-start
         (swb39-l-size)
         (swb39-shift a9 index))
        0))
      (implies
       (not
        (equal
         (swb39-havoc6-value
          protected-start
          (swb39-l-size)
          (swb39-shift a14 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= lower index)
         (implies
          (< index upper)
          (implies
           (< index (swb39-l-size))
           (not
            (swb39-idle-core-havoc6-p
             protected-start
             (swb39-l-size)
             index)))))))))))

(defun-sk swb39-a14-selected-or-not-idle-p
    (protected-start a14 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-havoc6-value
         protected-start
         (swb39-l-size)
         (swb39-shift a14 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb39-l-size))
        (or
         (not
          (equal
           (swb39-havoc6-value
            protected-start
            (swb39-l-size)
            (swb39-shift a17 index))
           0))
         (not
          (swb39-idle-core-havoc6-p
           protected-start
           (swb39-l-size)
           index)))))))))

;; Pointed-to mask addresses and the quantified memory-layout hypotheses.

(defun swb39-pointed-array-mask (a index)
  (swb39-shift
   (swb39-t8
    (swb39-shift
     (swb39-shift a index)
     0))
   0))

(defun-sk swb39-array-layout-p (which a bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (and
        (swb39-valid-rd-p
         which
         (swb39-shift a index)
         1)
        (swb39-valid-rw-p
         which
         (swb39-pointed-array-mask a index)
         bound)))))))

(defun-sk swb39-separated-from-array-p
    (mask mask-length a bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (swb39-separated-p
        mask
        mask-length
        (swb39-pointed-array-mask a index)
        bound))))))

(defun swb39-pointed-field-mask (field-address)
  (swb39-shift
   (swb39-t8
    (swb39-shift field-address 0))
   0))

(defun-sk swb39-sched-group-cpus-layout-p
    (which a bound)
  (forall (address)
    (implies
     (swb39-address-p address)
     (let*
         ((field
           (swb39-l-sched-group-cpus address))
          (mask
           (swb39-pointed-field-mask field)))
       (and
        (swb39-valid-rd-p which field 1)
        (swb39-valid-rd-p which mask bound)
        (swb39-separated-from-array-p
         mask bound a bound))))))

(defun-sk swb39-sched-group-mask-layout-p
    (which a bound)
  (forall (address)
    (implies
     (swb39-address-p address)
     (let*
         ((field
           (swb39-l-sched-group-mask address))
          (mask
           (swb39-pointed-field-mask field)))
       (and
        (swb39-valid-rd-p which field 1)
        (swb39-valid-rd-p which mask bound)
        (swb39-separated-from-array-p
         mask bound a bound))))))

(defun-sk swb39-group-balance-mask-layout-p
    (which a bound)
  (forall (address)
    (implies
     (swb39-address-p address)
     (let*
         ((field
           (swb39-l-group-balance-mask address))
          (mask
           (swb39-pointed-field-mask field)))
       (and
        (swb39-valid-rd-p which field 1)
        (swb39-valid-rd-p which mask bound)
        (swb39-separated-from-array-p
         mask bound a bound))))))

(defun-sk swb39-cpu-smt-layout-p (which a bound)
  (forall (cpu)
    (implies
     (integerp cpu)
     (implies
      (<= 0 cpu)
      (implies
       (< cpu bound)
       (let*
           ((field
             (swb39-l-cpu-smt-mask cpu))
            (mask
             (swb39-pointed-field-mask field)))
         (and
          (swb39-valid-rd-p which field 1)
          (swb39-valid-rd-p which mask bound)
          (swb39-separated-from-array-p
           mask bound a bound))))))))

;; Quantified havoc-agreement and final loop-invariant clauses.

(defun-sk swb39-havoc5-agreement-p
    (protected-start a14 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb39-l-size))
       (iff
        (not
         (equal
          (swb39-havoc5-value
           protected-start
           (swb39-l-size)
           (swb39-shift a14 index))
          0))
        (not
         (equal
          (swb39-havoc5-value
           protected-start
           (swb39-l-size)
           (swb39-shift a17 index))
          0))))))))

(defun-sk swb39-havoc6-a17-implies-a14-p
    (protected-start a17 a14)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-havoc6-value
         protected-start
         (swb39-l-size)
         (swb39-shift a17 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb39-l-size))
        (not
         (equal
          (swb39-havoc6-value
           protected-start
           (swb39-l-size)
           (swb39-shift a14 index))
          0))))))))

(defun-sk swb39-t7-selected-not-idle-p (a9 a14)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-t7 (swb39-shift a9 index))
        0))
      (implies
       (not
        (equal
         (swb39-t7 (swb39-shift a14 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index (swb39-l-size))
         (not
          (swb39-idle-core-t7-p index)))))))))

(defun-sk swb39-t7-selected-prefix-idle-zero-p
    (a9 a14 upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb39-t7 (swb39-shift a9 index))
        0))
      (implies
       (not
        (equal
         (swb39-t7 (swb39-shift a14 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index upper)
         (implies
          (< index (swb39-l-size))
          (equal
           (swb39-l-idle-cpu index)
           0)))))))))

;; The complete source verification condition, with source let-bindings kept
;; as definitional ACL2 let-bindings and all source quantifier scopes intact.

(defun swb39-goal-body
    (a1 a i i8 i3 i9 i5 i6 i1 i2 i4 i7 i10)
  (implies
     (and
      (swb39-address-p a1)
      (swb39-address-p a)
      (integerp i)
      (integerp i8)
      (integerp i3)
      (integerp i9)
      (integerp i5)
      (integerp i6)
      (integerp i1)
      (integerp i2)
      (integerp i4)
      (integerp i7)
      (integerp i10)
      (swb39-function-types-p)
      (swb39-mask-schema-types-p)
      (swb39-zero-mask-memory-instance-p)
      (swb39-q-mask-refl-p)
      (swb39-q-mask-symm-p)
      (swb39-q-mask-trans-p)
      (swb39-mask-t8-instance-p)
      (swb39-mask-t7-instance-p)
      (integerp (swb39-l-size))
      (< 0 (swb39-l-size))
      (<= (swb39-l-size) 2147483647))
     (let*
         ((a2 (swb39-shift a1 3))
          (x (swb39-t7 a2))
          (a3 (swb39-shift a1 0))
          (a4 (swb39-t8 a3))
          (a5 (swb39-shift a4 1))
          (x1 (swb39-t7 a5))
          (a6 (swb39-shift a1 4))
          (a7 (swb39-t8 a6))
          (a8 (swb39-shift a7 0))
          (a9 (swb39-t8 a8))
          (a10 (swb39-shift a1 1))
          (x2 (swb39-t7 a10))
          (x3
           (swb39-t7
            (swb39-shift a9 x2)))
          (a11 (swb39-shift a4 0))
          (a12 (swb39-t8 a11))
          (a13
           (swb39-l-group-balance-mask a12))
          (a14
           (swb39-t8
            (swb39-shift a13 0)))
          (a15 (swb39-shift a i))
          (a16 (swb39-shift a15 0))
          (a17 (swb39-t8 a16))
          (a18 (swb39-shift a17 0))
          (a19 (swb39-shift a9 0))
          (a21
           (swb39-havoc6-value
            a18
            (swb39-l-size)
            (swb39-shift a17 i8)))
          (a22
           (swb39-havoc6-value
            a18
            (swb39-l-size)
            (swb39-shift a9 i3)))
          (a23
           (swb39-havoc6-value
            a18
            (swb39-l-size)
            (swb39-shift a9 i8)))
          (a24
           (swb39-havoc6-value
            a18
            (swb39-l-size)
            (swb39-shift a14 i3)))
          (a25
           (swb39-havoc6-value
            a18
            (swb39-l-size)
            a5))
          (a26 (swb39-shift a14 0))
          (a27
           (swb39-havoc6-value
            a18
            (swb39-l-size)
            a10))
          (x4 (swb39-land 7 a25))
          (x5 (swb39-to-uint32 i9)))
       (implies
        (and
         (swb39-mask-havoc6-instance-p a18)
         (swb39-mask-havoc5-instance-p a18)
         (not (equal (swb39-l-idle-cpu i5) 0))
         (not (equal (swb39-l-idle-cpu i6) 0))
         (not (equal x 2))
         (equal (swb39-land 7 x1) 0)
         (not
          (equal
           (swb39-t7 (swb39-shift a9 i5))
           0))
         (not
          (equal
           (swb39-t7 (swb39-shift a9 i6))
           0))
         (not (equal x3 0))
         (not
          (equal
           (swb39-t7 (swb39-shift a14 i5))
           0))
         (not
          (equal
           (swb39-t7 (swb39-shift a14 i6))
           0))
         (<= 0 i)
         (< i (swb39-l-size))
         (<= 0 i5)
         (< i5 (swb39-l-size))
         (<= 0 i6)
         (< i6 (swb39-l-size))
         (<= 0 i9)
         (<= i9 (swb39-l-size))
         (<= 0 x2)
         (< x2 (swb39-l-size))
         (<= (swb39-region
              (swb39-address-base a))
             0)
         (<= (swb39-region
              (swb39-address-base a1))
             0)
         (swb39-framed-p)
         (swb39-linked-p)
         (swb39-is-uint32-p i)
         (swb39-is-uint32-p i1)
         (swb39-is-sint32-p i2)
         (swb39-is-sint32-p i3)
         (swb39-is-sint32-p i4)
         (swb39-is-sint32-p i7)
         (swb39-is-sint32-p i8)
         (swb39-is-sint32-p i9)
         (swb39-is-sint32-p i10)
         (swb39-valid-rd-p :t a1 5)
         (swb39-is-uint32-p x)
         (swb39-is-sint32-p x2)
         (swb39-valid-rd-p :t a6 1)
         (swb39-valid-rd-p :t a10 1)
         (swb39-valid-rd-p :t a2 1)
         (swb39-valid-rd-p :t a3 1)
         (swb39-valid-rd-p :t a15 1)
         (swb39-valid-rd-p :t a7 1)
         (swb39-valid-rd-p
          :t
          (swb39-t8 (swb39-shift a1 2))
          2)
         (swb39-valid-rd-p :t a4 2)
         (swb39-is-sint32-p x1)
         (swb39-valid-rd-p :t a16 1)
         (swb39-valid-rd-p :t a8 1)
         (swb39-valid-rd-p :t a11 1)
         (swb39-valid-rd-p :t a12 1)
         (swb39-valid-rd-p :t a13 1)
         (swb39-is-uint8-p x3)
         (swb39-valid-rd-p
          :t a18 (swb39-l-size))
         (swb39-valid-rd-p
          :t a19 (swb39-l-size))
         (swb39-valid-rw-p
          :t a18 (swb39-l-size))
         (swb39-is-uint8-p a21)
         (swb39-is-uint8-p a22)
         (swb39-is-uint8-p a23)
         (swb39-is-uint8-p a24)
         (swb39-is-sint32-p a25)
         (swb39-valid-rd-p
          :t a26 (swb39-l-size))
         (swb39-separated-p
          a18
          (swb39-l-size)
          a26
          (swb39-l-size))
         (if
             (< (swb39-to-uint32 i8)
                (swb39-l-size))
             (and
              (equal i10 i8)
              (swb39-allocations-equal-p
               :t4 :t)
              (not
               (equal
                (swb39-l-idle-cpu i10)
                0))
              (equal
               (if (equal a27 i10) 1 0)
               i2)
              (<= 0 i10)
              (< i10 (swb39-l-size))
              (swb39-valid-rd-p :t4 a10 1)
              (swb39-valid-rd-p :t4 a3 1)
              (swb39-valid-rd-p :t4 a5 1)
              (or
               (not (equal x4 0))
               (and
                (equal (swb39-l-size) i1)
                (swb39-idle-core-havoc6-p
                 a18 i1 i10)
                (swb39-array-layout-p
                 :t4 a i1)
                (swb39-sched-group-cpus-layout-p
                 :t4 a i1)
                (swb39-sched-group-mask-layout-p
                 :t4 a i1)
                (swb39-group-balance-mask-layout-p
                 :t4 a i1)
                (swb39-cpu-smt-layout-p
                 :t4 a i1))))
           (and
            (equal i4 i3)
            (swb39-allocations-equal-p
             :t1 :t)
            (if
                (equal i4 -1)
                (and
                 (swb39-allocations-equal-p
                  :t2 :t1)
                 (equal
                  (swb39-l-group-balance-cpu a12)
                  i7)
                 (equal
                  (if (equal a27 i7) 1 0)
                  i2)
                 (swb39-valid-rd-p :t2 a10 1))
              (and
               (swb39-allocations-equal-p
                :t3 :t1)
               (equal
                (if (equal a27 i4) 1 0)
                i2)
               (swb39-valid-rd-p :t3 a10 1)))))
         (implies
          (not (equal x4 0))
          (equal i3 -1))
         (implies
          (not (equal i3 -1))
          (and
           (not
            (equal
             (swb39-l-idle-cpu i3)
             0))
           (not (equal a22 0))
           (not (equal a24 0))
           (<= 0 i3)
           (< i3 (swb39-l-size))))
         (implies
          (equal i3 -1)
          (swb39-a14-selection-implies-a17-p
           a18 a14 a17))
         (implies
          (swb39-selected-tail-exists-p
           a18 a17 a9 x5)
          (< i8 (swb39-l-size)))
         (implies
          (swb39-selected-tail-exists-p
           a18 a17 a9 x5)
          (and
           (< i8 (swb39-l-size))
           (<= x5 i8)))
         (implies
          (swb39-selected-tail-exists-p
           a18 a17 a9 x5)
          (and
           (not (equal a21 0))
           (not (equal a23 0))))
         (implies
          (swb39-no-selected-tail-p
           a18 a17 a9 x5)
          (equal (swb39-l-size) i8))
         (implies
          (not (equal i3 -1))
          (swb39-selected-prefix-idle-zero-p
           a18 a9 a14 i3))
         (implies
          (equal i3 -1)
          (swb39-selected-prefix-idle-zero-p
           a18 a9 a14 i9))
         (implies
          (swb39-selected-tail-exists-p
           a18 a17 a9 x5)
          (swb39-no-selected-prefix-p
           a18 a17 a9 x5 i8))
         (implies
          (not (equal i3 -1))
          (swb39-selected-range-not-idle-p
           a18 a9 a14 i3 i9))
         (implies
          (not (equal i3 -1))
          (swb39-a14-selected-or-not-idle-p
           a18 a14 a17))
         (swb39-separated-from-array-p
          a19
          (swb39-l-size)
          a
          (swb39-l-size))
         (swb39-array-layout-p
          :t a (swb39-l-size))
         (swb39-havoc5-agreement-p
          a18 a14 a17)
         (swb39-havoc6-a17-implies-a14-p
          a18 a17 a14)
         (swb39-t7-selected-not-idle-p
          a9 a14)
         (swb39-t7-selected-prefix-idle-zero-p
          a9 a14 i6)
         (swb39-sched-group-cpus-layout-p
          :t a (swb39-l-size))
         (swb39-sched-group-mask-layout-p
          :t a (swb39-l-size))
         (swb39-group-balance-mask-layout-p
          :t a (swb39-l-size))
         (swb39-cpu-smt-layout-p
          :t a (swb39-l-size)))
        (iff
         (equal x2 i6)
         (not (equal i2 0)))))))

(defun-sk
    ntp4vc-should-we-balance-not-newly-idle-with-idle-cpu-post-2-goal39-statement
    ()
  (forall
      (a1 a i i8 i3 i9 i5 i6 i1 i2 i4 i7 i10)
    (swb39-goal-body
     a1 a i i8 i3 i9 i5 i6 i1 i2 i4 i7 i10)))

(value-triple :itpeval-statement-checked)

:q
