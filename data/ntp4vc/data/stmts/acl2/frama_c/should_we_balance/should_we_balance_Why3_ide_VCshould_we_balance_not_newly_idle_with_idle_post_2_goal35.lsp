;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_not_newly_idle_with_idle_post_2_goal35:
;; the should-we-balance postcondition for a non-newly-idle case when an idle
;; CPU is available, with integer bounds, memory validity, framing, separation,
;; havoc-memory agreement, and quantified CPU-mask layout conditions. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb35-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb35-address-base (address)
  (car address))

(defun swb35-address-offset (address)
  (cdr address))

(defun swb35-shift (address amount)
  (cons
   (swb35-address-base address)
   (+ (swb35-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memories, allocation
;; maps, and fixed symbols.

(defstub swb35-t7 (address) t)
(defstub swb35-t6 (address) t)
(defstub swb35-t5 (address) t)
(defstub swb35-t8 (address) t)

(defstub swb35-allocation-t (index) t)
(defstub swb35-allocation-t4 (index) t)
(defstub swb35-allocation-t1 (index) t)
(defstub swb35-allocation-t2 (index) t)
(defstub swb35-allocation-t3 (index) t)

(defstub swb35-region (base) t)
(defstub swb35-linked-op () t)
(defstub swb35-l-size () t)
(defstub swb35-mask-memory-apply (memory-symbol address) t)
(defstub swb35-mask-pointer-apply (pointer-symbol address) t)
(defstub swb35-l-idle-cpu (index) t)
(defstub swb35-l-sched-group-cpus (address) t)
(defstub swb35-l-sched-group-mask (address) t)
(defstub swb35-l-group-balance-mask (address) t)
(defstub swb35-l-group-balance-cpu (address) t)
(defstub swb35-l-cpu-smt-mask (index) t)

(defun swb35-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb35-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb35-address-p address)
      (and
       (integerp
        (swb35-mask-memory-apply
         memory-symbol address))
       (swb35-address-p
        (swb35-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb35-is-uint8-p
        (swb35-l-idle-cpu index))
       (swb35-address-p
        (swb35-l-cpu-smt-mask index)))))))

(defun-sk swb35-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb35-address-p address)
     (equal
      (swb35-mask-memory-apply
       'swb35-zero-memory address)
      0))))

(defun-sk swb35-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb35-l-size)))
     (not
      (equal
       (swb35-mask-memory-apply
        memory-symbol
        (swb35-shift
         (swb35-mask-pointer-apply
          pointer-symbol
          (swb35-shift
           (swb35-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb35-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb35-mask-memory-apply
         memory-symbol
         (swb35-shift
          (swb35-mask-pointer-apply
           pointer-symbol
           (swb35-shift
            (swb35-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb35-l-size))
      (<= 0 j)
      (< j (swb35-l-size)))
     (not
      (equal
       (swb35-mask-memory-apply
        memory-symbol
        (swb35-shift
         (swb35-mask-pointer-apply
          pointer-symbol
          (swb35-shift
           (swb35-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb35-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb35-mask-memory-apply
         memory-symbol
         (swb35-shift
          (swb35-mask-pointer-apply
           pointer-symbol
           (swb35-shift
            (swb35-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb35-mask-memory-apply
         memory-symbol
         (swb35-shift
          (swb35-mask-pointer-apply
           pointer-symbol
           (swb35-shift
            (swb35-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb35-l-size))
      (<= 0 j)
      (< j (swb35-l-size))
      (<= 0 k)
      (< k (swb35-l-size)))
     (not
      (equal
       (swb35-mask-memory-apply
        memory-symbol
        (swb35-shift
         (swb35-mask-pointer-apply
          pointer-symbol
          (swb35-shift
           (swb35-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb35-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb35-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Preserve every source function type over the full unbounded integer and
;; address domains, together with the imported idle-CPU range property.

(defun-sk swb35-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb35-address-p address)
      (and
       (integerp (swb35-t7 address))
       (integerp (swb35-t6 address))
       (integerp (swb35-t5 address))
       (swb35-address-p (swb35-t8 address))
       (swb35-address-p
        (swb35-l-sched-group-cpus address))
       (swb35-address-p
        (swb35-l-sched-group-mask address))
       (swb35-address-p
        (swb35-l-group-balance-mask address))
       (integerp
        (swb35-l-group-balance-cpu address))))
     (implies
      (integerp index)
      (and
       (integerp (swb35-allocation-t index))
       (integerp (swb35-allocation-t4 index))
       (integerp (swb35-allocation-t1 index))
       (integerp (swb35-allocation-t2 index))
       (integerp (swb35-allocation-t3 index))
       (swb35-is-uint8-p (swb35-l-idle-cpu index))
       (swb35-address-p (swb35-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb35-region base))))))

(defun swb35-linked-p ()
  (if (swb35-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32), and Cbits.land is
;; mathematical bitwise conjunction on integers.

(defun swb35-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun swb35-land (left right)
  (logand left right))

;; A finite selector is only a definitional abbreviation for the five named
;; source allocation maps.

(defun swb35-allocation-value (which index)
  (cond
   ((equal which :t4)
    (swb35-allocation-t4 index))
   ((equal which :t1)
    (swb35-allocation-t1 index))
   ((equal which :t2)
    (swb35-allocation-t2 index))
   ((equal which :t3)
    (swb35-allocation-t3 index))
   (t
    (swb35-allocation-t index))))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb35-valid-rw-p (which address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb35-address-base address))
    (<= 0 (swb35-address-offset address))
    (<=
     (+ (swb35-address-offset address) length)
     (swb35-allocation-value
      which
      (swb35-address-base address))))))

(defun swb35-valid-rd-p (which address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb35-address-base address)))
    (<= 0 (swb35-address-offset address))
    (<=
     (+ (swb35-address-offset address) length)
     (swb35-allocation-value
      which
      (swb35-address-base address))))))

(defun swb35-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb35-address-base left)
     (swb35-address-base right)))
   (<=
    (+ (swb35-address-offset right) right-length)
    (swb35-address-offset left))
   (<=
    (+ (swb35-address-offset left) left-length)
    (swb35-address-offset right))))

;; Exact function equality for the allocation maps appearing in the branch
;; conditions.

(defun-sk swb35-allocations-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (swb35-allocation-value left index)
      (swb35-allocation-value right index)))))

;; Exact unfolding of Memory.framed for t_8.

(defun-sk swb35-framed-p ()
  (forall (address)
    (implies
     (swb35-address-p address)
     (<=
      (swb35-region
       (swb35-address-base (swb35-t8 address)))
      0))))

;; Exact havoc_access values a_20 = havoc t_6 t_7 and
;; a_28 = havoc t_5 t_7.

(defun swb35-havoc6-value
    (protected-start protected-length query)
  (if
      (swb35-separated-p
       query 1 protected-start protected-length)
      (swb35-t7 query)
    (swb35-t6 query)))

(defun swb35-havoc5-value
    (protected-start protected-length query)
  (if
      (swb35-separated-p
       query 1 protected-start protected-length)
      (swb35-t7 query)
    (swb35-t5 query)))

;; Exact unfoldings of p_idle_core for the two memories used by this VC.

(defun-sk swb35-idle-core-havoc6-p
    (protected-start protected-length cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-havoc6-value
         protected-start
         protected-length
         (swb35-shift
          (swb35-t8
           (swb35-shift
            (swb35-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb35-l-size))
        (not
         (equal
          (swb35-l-idle-cpu index)
          0))))))))

(defun-sk swb35-idle-core-t7-p (cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-t7
         (swb35-shift
          (swb35-t8
           (swb35-shift
            (swb35-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb35-l-size))
        (not
         (equal
          (swb35-l-idle-cpu index)
          0))))))))

;; The existential paired-selection condition shared by several hypotheses.

(defun-sk swb35-selected-tail-exists-p
    (protected-start a17 a9 lower)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swb35-havoc6-value
        protected-start
        (swb35-l-size)
        (swb35-shift a17 index))
       0))
     (not
      (equal
       (swb35-havoc6-value
        protected-start
        (swb35-l-size)
        (swb35-shift a9 index))
       0))
     (< index (swb35-l-size))
     (<= lower index))))

;; Quantified selection and idle-core conditions from the loop invariants.

(defun-sk swb35-a14-selection-implies-a17-p
    (protected-start a14 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-havoc6-value
         protected-start
         (swb35-l-size)
         (swb35-shift a14 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb35-l-size))
        (not
         (equal
          (swb35-havoc6-value
           protected-start
           (swb35-l-size)
           (swb35-shift a17 index))
          0))))))))

(defun-sk swb35-no-selected-tail-p
    (protected-start a17 a9 lower)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index (swb35-l-size))
      (implies
       (<= lower index)
       (or
        (equal
         (swb35-havoc6-value
          protected-start
          (swb35-l-size)
          (swb35-shift a17 index))
         0)
        (equal
         (swb35-havoc6-value
          protected-start
          (swb35-l-size)
          (swb35-shift a9 index))
         0)))))))

(defun-sk swb35-no-selected-prefix-p
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
         (swb35-havoc6-value
          protected-start
          (swb35-l-size)
          (swb35-shift a17 index))
         0)
        (equal
         (swb35-havoc6-value
          protected-start
          (swb35-l-size)
          (swb35-shift a9 index))
         0)))))))

(defun-sk swb35-selected-prefix-idle-zero-p
    (protected-start a9 a14 upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-havoc6-value
         protected-start
         (swb35-l-size)
         (swb35-shift a9 index))
        0))
      (implies
       (not
        (equal
         (swb35-havoc6-value
          protected-start
          (swb35-l-size)
          (swb35-shift a14 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index upper)
         (implies
          (< index (swb35-l-size))
          (equal
           (swb35-l-idle-cpu index)
           0)))))))))

(defun-sk swb35-selected-range-not-idle-p
    (protected-start a9 a14 lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-havoc6-value
         protected-start
         (swb35-l-size)
         (swb35-shift a9 index))
        0))
      (implies
       (not
        (equal
         (swb35-havoc6-value
          protected-start
          (swb35-l-size)
          (swb35-shift a14 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= lower index)
         (implies
          (< index upper)
          (implies
           (< index (swb35-l-size))
           (not
            (swb35-idle-core-havoc6-p
             protected-start
             (swb35-l-size)
             index)))))))))))

(defun-sk swb35-a14-selected-or-not-idle-p
    (protected-start a14 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-havoc6-value
         protected-start
         (swb35-l-size)
         (swb35-shift a14 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb35-l-size))
        (or
         (not
          (equal
           (swb35-havoc6-value
            protected-start
            (swb35-l-size)
            (swb35-shift a17 index))
           0))
         (not
          (swb35-idle-core-havoc6-p
           protected-start
           (swb35-l-size)
           index)))))))))

;; Pointed-to mask addresses and the quantified memory-layout hypotheses.

(defun swb35-pointed-array-mask (a index)
  (swb35-shift
   (swb35-t8
    (swb35-shift
     (swb35-shift a index)
     0))
   0))

(defun-sk swb35-array-layout-p (which a bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (and
        (swb35-valid-rd-p
         which
         (swb35-shift a index)
         1)
        (swb35-valid-rw-p
         which
         (swb35-pointed-array-mask a index)
         bound)))))))

(defun-sk swb35-separated-from-array-p
    (mask mask-length a bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (swb35-separated-p
        mask
        mask-length
        (swb35-pointed-array-mask a index)
        bound))))))

(defun swb35-pointed-field-mask (field-address)
  (swb35-shift
   (swb35-t8
    (swb35-shift field-address 0))
   0))

(defun-sk swb35-sched-group-cpus-layout-p
    (which a bound)
  (forall (address)
    (implies
     (swb35-address-p address)
     (let*
         ((field
           (swb35-l-sched-group-cpus address))
          (mask
           (swb35-pointed-field-mask field)))
       (and
        (swb35-valid-rd-p which field 1)
        (swb35-valid-rd-p which mask bound)
        (swb35-separated-from-array-p
         mask bound a bound))))))

(defun-sk swb35-sched-group-mask-layout-p
    (which a bound)
  (forall (address)
    (implies
     (swb35-address-p address)
     (let*
         ((field
           (swb35-l-sched-group-mask address))
          (mask
           (swb35-pointed-field-mask field)))
       (and
        (swb35-valid-rd-p which field 1)
        (swb35-valid-rd-p which mask bound)
        (swb35-separated-from-array-p
         mask bound a bound))))))

(defun-sk swb35-group-balance-mask-layout-p
    (which a bound)
  (forall (address)
    (implies
     (swb35-address-p address)
     (let*
         ((field
           (swb35-l-group-balance-mask address))
          (mask
           (swb35-pointed-field-mask field)))
       (and
        (swb35-valid-rd-p which field 1)
        (swb35-valid-rd-p which mask bound)
        (swb35-separated-from-array-p
         mask bound a bound))))))

(defun-sk swb35-cpu-smt-layout-p (which a bound)
  (forall (cpu)
    (implies
     (integerp cpu)
     (implies
      (<= 0 cpu)
      (implies
       (< cpu bound)
       (let*
           ((field
             (swb35-l-cpu-smt-mask cpu))
            (mask
             (swb35-pointed-field-mask field)))
         (and
          (swb35-valid-rd-p which field 1)
          (swb35-valid-rd-p which mask bound)
          (swb35-separated-from-array-p
           mask bound a bound))))))))

;; Quantified havoc-agreement and final loop-invariant clauses.

(defun-sk swb35-havoc5-agreement-p
    (protected-start a14 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb35-l-size))
       (iff
        (not
         (equal
          (swb35-havoc5-value
           protected-start
           (swb35-l-size)
           (swb35-shift a14 index))
          0))
        (not
         (equal
          (swb35-havoc5-value
           protected-start
           (swb35-l-size)
           (swb35-shift a17 index))
          0))))))))

(defun-sk swb35-havoc6-a17-implies-a14-p
    (protected-start a17 a14)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-havoc6-value
         protected-start
         (swb35-l-size)
         (swb35-shift a17 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb35-l-size))
        (not
         (equal
          (swb35-havoc6-value
           protected-start
           (swb35-l-size)
           (swb35-shift a14 index))
          0))))))))

(defun-sk swb35-t7-selected-prefix-idle-zero-p
    (a9 a14 upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb35-t7 (swb35-shift a9 index))
        0))
      (implies
       (not
        (equal
         (swb35-t7 (swb35-shift a14 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index upper)
         (implies
          (< index (swb35-l-size))
          (equal
           (swb35-l-idle-cpu index)
           0)))))))))

;; The complete source verification condition, with source let-bindings kept
;; as definitional ACL2 let-bindings and all source quantifier scopes intact.

(defun swb35-goal-body
    (a1 a i i8 i3 i9 i5 i6 i1 i2 i4 i7 i10)
  (implies
     (and
      (swb35-address-p a1)
      (swb35-address-p a)
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
      (swb35-function-types-p)
      (swb35-scheduler-schema-types-p)
      (swb35-zero-mask-memory-instance-p)
      (swb35-q-mask-refl-p)
      (swb35-q-mask-symm-p)
      (swb35-q-mask-trans-p)
      (integerp (swb35-l-size))
      (< 0 (swb35-l-size))
      (<= (swb35-l-size) 2147483647))
     (let*
         ((a2 (swb35-shift a1 3))
          (x (swb35-t7 a2))
          (a3 (swb35-shift a1 0))
          (a4 (swb35-t8 a3))
          (a5 (swb35-shift a4 1))
          (x1 (swb35-t7 a5))
          (a6 (swb35-shift a1 4))
          (a7 (swb35-t8 a6))
          (a8 (swb35-shift a7 0))
          (a9 (swb35-t8 a8))
          (a10 (swb35-shift a1 1))
          (x2 (swb35-t7 a10))
          (x3
           (swb35-t7
            (swb35-shift a9 x2)))
          (a11 (swb35-shift a4 0))
          (a12 (swb35-t8 a11))
          (a13
           (swb35-l-group-balance-mask a12))
          (a14
           (swb35-t8
            (swb35-shift a13 0)))
          (a15 (swb35-shift a i))
          (a16 (swb35-shift a15 0))
          (a17 (swb35-t8 a16))
          (a18 (swb35-shift a17 0))
          (a19 (swb35-shift a9 0))
          (a21
           (swb35-havoc6-value
            a18
            (swb35-l-size)
            (swb35-shift a17 i8)))
          (a22
           (swb35-havoc6-value
            a18
            (swb35-l-size)
            (swb35-shift a9 i3)))
          (a23
           (swb35-havoc6-value
            a18
            (swb35-l-size)
            (swb35-shift a9 i8)))
          (a24
           (swb35-havoc6-value
            a18
            (swb35-l-size)
            (swb35-shift a14 i3)))
          (a25
           (swb35-havoc6-value
            a18
            (swb35-l-size)
            a5))
          (a26 (swb35-shift a14 0))
          (a27
           (swb35-havoc6-value
            a18
            (swb35-l-size)
            a10))
          (x4 (swb35-land 7 a25))
          (x5 (swb35-to-uint32 i9)))
       (implies
        (and
         (not (equal (swb35-l-idle-cpu i5) 0))
         (not (equal (swb35-l-idle-cpu i6) 0))
         (not (equal x 2))
         (not (equal (swb35-land 7 x1) 0))
         (not
          (equal
           (swb35-t7 (swb35-shift a9 i5))
           0))
         (not
          (equal
           (swb35-t7 (swb35-shift a9 i6))
           0))
         (not (equal x3 0))
         (not
          (equal
           (swb35-t7 (swb35-shift a14 i5))
           0))
         (not
          (equal
           (swb35-t7 (swb35-shift a14 i6))
           0))
         (<= 0 i)
         (< i (swb35-l-size))
         (<= 0 i5)
         (< i5 (swb35-l-size))
         (<= 0 i6)
         (< i6 (swb35-l-size))
         (<= 0 i9)
         (<= i9 (swb35-l-size))
         (<= 0 x2)
         (< x2 (swb35-l-size))
         (<= (swb35-region
              (swb35-address-base a))
             0)
         (<= (swb35-region
              (swb35-address-base a1))
             0)
         (swb35-framed-p)
         (swb35-linked-p)
         (swb35-is-uint32-p i)
         (swb35-is-uint32-p i1)
         (swb35-is-sint32-p i2)
         (swb35-is-sint32-p i3)
         (swb35-is-sint32-p i4)
         (swb35-is-sint32-p i7)
         (swb35-is-sint32-p i8)
         (swb35-is-sint32-p i9)
         (swb35-is-sint32-p i10)
         (swb35-valid-rd-p :t a1 5)
         (swb35-is-uint32-p x)
         (swb35-is-sint32-p x2)
         (swb35-valid-rd-p :t a6 1)
         (swb35-valid-rd-p :t a10 1)
         (swb35-valid-rd-p :t a2 1)
         (swb35-valid-rd-p :t a3 1)
         (swb35-valid-rd-p :t a15 1)
         (swb35-valid-rd-p :t a7 1)
         (swb35-valid-rd-p
          :t
          (swb35-t8 (swb35-shift a1 2))
          2)
         (swb35-valid-rd-p :t a4 2)
         (swb35-is-sint32-p x1)
         (swb35-valid-rd-p :t a16 1)
         (swb35-valid-rd-p :t a8 1)
         (swb35-valid-rd-p :t a11 1)
         (swb35-valid-rd-p :t a12 1)
         (swb35-valid-rd-p :t a13 1)
         (swb35-is-uint8-p x3)
         (swb35-valid-rd-p
          :t a18 (swb35-l-size))
         (swb35-valid-rd-p
          :t a19 (swb35-l-size))
         (swb35-valid-rw-p
          :t a18 (swb35-l-size))
         (swb35-is-uint8-p a21)
         (swb35-is-uint8-p a22)
         (swb35-is-uint8-p a23)
         (swb35-is-uint8-p a24)
         (swb35-is-sint32-p a25)
         (swb35-valid-rd-p
          :t a26 (swb35-l-size))
         (swb35-separated-p
          a18
          (swb35-l-size)
          a26
          (swb35-l-size))
         (if
             (< (swb35-to-uint32 i8)
                (swb35-l-size))
             (and
              (equal i10 i8)
              (swb35-allocations-equal-p
               :t4 :t)
              (not
               (equal
                (swb35-l-idle-cpu i10)
                0))
              (equal
               (if (equal a27 i10) 1 0)
               i2)
              (<= 0 i10)
              (< i10 (swb35-l-size))
              (swb35-valid-rd-p :t4 a10 1)
              (swb35-valid-rd-p :t4 a3 1)
              (swb35-valid-rd-p :t4 a5 1)
              (or
               (not (equal x4 0))
               (and
                (equal (swb35-l-size) i1)
                (swb35-idle-core-havoc6-p
                 a18 i1 i10)
                (swb35-array-layout-p
                 :t4 a i1)
                (swb35-sched-group-cpus-layout-p
                 :t4 a i1)
                (swb35-sched-group-mask-layout-p
                 :t4 a i1)
                (swb35-group-balance-mask-layout-p
                 :t4 a i1)
                (swb35-cpu-smt-layout-p
                 :t4 a i1))))
           (and
            (equal i4 i3)
            (swb35-allocations-equal-p
             :t1 :t)
            (if
                (equal i4 -1)
                (and
                 (swb35-allocations-equal-p
                  :t2 :t1)
                 (equal
                  (swb35-l-group-balance-cpu a12)
                  i7)
                 (equal
                  (if (equal a27 i7) 1 0)
                  i2)
                 (swb35-valid-rd-p :t2 a10 1))
              (and
               (swb35-allocations-equal-p
                :t3 :t1)
               (equal
                (if (equal a27 i4) 1 0)
                i2)
               (swb35-valid-rd-p :t3 a10 1)))))
         (implies
          (not (equal x4 0))
          (equal i3 -1))
         (implies
          (not (equal i3 -1))
          (and
           (not
            (equal
             (swb35-l-idle-cpu i3)
             0))
           (not (equal a22 0))
           (not (equal a24 0))
           (<= 0 i3)
           (< i3 (swb35-l-size))))
         (implies
          (equal i3 -1)
          (swb35-a14-selection-implies-a17-p
           a18 a14 a17))
         (implies
          (swb35-selected-tail-exists-p
           a18 a17 a9 x5)
          (< i8 (swb35-l-size)))
         (implies
          (swb35-selected-tail-exists-p
           a18 a17 a9 x5)
          (and
           (< i8 (swb35-l-size))
           (<= x5 i8)))
         (implies
          (swb35-selected-tail-exists-p
           a18 a17 a9 x5)
          (and
           (not (equal a21 0))
           (not (equal a23 0))))
         (implies
          (swb35-no-selected-tail-p
           a18 a17 a9 x5)
          (equal (swb35-l-size) i8))
         (implies
          (not (equal i3 -1))
          (swb35-selected-prefix-idle-zero-p
           a18 a9 a14 i3))
         (implies
          (equal i3 -1)
          (swb35-selected-prefix-idle-zero-p
           a18 a9 a14 i9))
         (implies
          (swb35-selected-tail-exists-p
           a18 a17 a9 x5)
          (swb35-no-selected-prefix-p
           a18 a17 a9 x5 i8))
         (implies
          (not (equal i3 -1))
          (swb35-selected-range-not-idle-p
           a18 a9 a14 i3 i9))
         (implies
          (not (equal i3 -1))
          (swb35-a14-selected-or-not-idle-p
           a18 a14 a17))
         (swb35-separated-from-array-p
          a19
          (swb35-l-size)
          a
          (swb35-l-size))
         (swb35-array-layout-p
          :t a (swb35-l-size))
         (swb35-havoc5-agreement-p
          a18 a14 a17)
         (swb35-havoc6-a17-implies-a14-p
          a18 a17 a14)
         (swb35-t7-selected-prefix-idle-zero-p
          a9 a14 i6)
         (swb35-sched-group-cpus-layout-p
          :t a (swb35-l-size))
         (swb35-sched-group-mask-layout-p
          :t a (swb35-l-size))
         (swb35-group-balance-mask-layout-p
          :t a (swb35-l-size))
         (swb35-cpu-smt-layout-p
          :t a (swb35-l-size)))
        (iff
         (equal x2 i6)
         (not (equal i2 0)))))))

(defun-sk
    ntp4vc-should-we-balance-not-newly-idle-with-idle-post-2-goal35-statement
    ()
  (forall
      (a1 a i i8 i3 i9 i5 i6 i1 i2 i4 i7 i10)
    (swb35-goal-body
     a1 a i i8 i3 i9 i5 i6 i1 i2 i4 i7 i10)))

(value-triple :itpeval-statement-checked)

:q
