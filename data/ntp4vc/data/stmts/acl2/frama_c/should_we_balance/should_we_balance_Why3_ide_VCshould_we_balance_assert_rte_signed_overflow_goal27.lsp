;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_signed_overflow_goal27:
;; the conditional signed-32-bit overflow bound for the should-we-balance
;; indices under the stated integer ranges, memory validity, framing,
;; separation, havoc, CPU-mask layout, and quantified scheduling hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb27-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb27-address-base (address)
  (car address))

(defun swb27-address-offset (address)
  (cdr address))

(defun swb27-shift (address amount)
  (cons
   (swb27-address-base address)
   (+ (swb27-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memory functions t_1
;; through t_5, allocation map t, and the fixed source symbols.

(defstub swb27-t1 (address) t)
(defstub swb27-t2 (address) t)
(defstub swb27-t3 (address) t)
(defstub swb27-t4 (address) t)
(defstub swb27-t5 (address) t)
(defstub swb27-allocation (index) t)
(defstub swb27-region (base) t)
(defstub swb27-linked-op () t)
(defstub swb27-l-size () t)
(defstub swb27-mask-memory-apply (memory-symbol address) t)
(defstub swb27-mask-pointer-apply (pointer-symbol address) t)
(defstub swb27-l-idle-cpu (index) t)
(defstub swb27-l-sched-group-cpus (address) t)
(defstub swb27-l-sched-group-mask (address) t)
(defstub swb27-l-group-balance-mask (address) t)
(defstub swb27-l-cpu-smt-mask (index) t)

(defun swb27-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb27-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb27-address-p address)
      (and
       (integerp
        (swb27-mask-memory-apply
         memory-symbol address))
       (swb27-address-p
        (swb27-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb27-is-uint8-p
        (swb27-l-idle-cpu index))
       (swb27-address-p
        (swb27-l-cpu-smt-mask index)))))))

(defun-sk swb27-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb27-address-p address)
     (equal
      (swb27-mask-memory-apply
       'swb27-zero-memory address)
      0))))

(defun-sk swb27-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb27-l-size)))
     (not
      (equal
       (swb27-mask-memory-apply
        memory-symbol
        (swb27-shift
         (swb27-mask-pointer-apply
          pointer-symbol
          (swb27-shift
           (swb27-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb27-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb27-mask-memory-apply
         memory-symbol
         (swb27-shift
          (swb27-mask-pointer-apply
           pointer-symbol
           (swb27-shift
            (swb27-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb27-l-size))
      (<= 0 j)
      (< j (swb27-l-size)))
     (not
      (equal
       (swb27-mask-memory-apply
        memory-symbol
        (swb27-shift
         (swb27-mask-pointer-apply
          pointer-symbol
          (swb27-shift
           (swb27-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb27-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb27-mask-memory-apply
         memory-symbol
         (swb27-shift
          (swb27-mask-pointer-apply
           pointer-symbol
           (swb27-shift
            (swb27-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb27-mask-memory-apply
         memory-symbol
         (swb27-shift
          (swb27-mask-pointer-apply
           pointer-symbol
           (swb27-shift
            (swb27-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb27-l-size))
      (<= 0 j)
      (< j (swb27-l-size))
      (<= 0 k)
      (< k (swb27-l-size)))
     (not
      (equal
       (swb27-mask-memory-apply
        memory-symbol
        (swb27-shift
         (swb27-mask-pointer-apply
          pointer-symbol
          (swb27-shift
           (swb27-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb27-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb27-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun-sk swb27-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb27-address-p address)
      (and
       (integerp (swb27-t1 address))
       (integerp (swb27-t2 address))
       (integerp (swb27-t3 address))
       (integerp (swb27-t4 address))
       (swb27-address-p (swb27-t5 address))
       (swb27-address-p
        (swb27-l-sched-group-cpus address))
       (swb27-address-p
        (swb27-l-sched-group-mask address))
       (swb27-address-p
        (swb27-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb27-allocation index))
       (swb27-is-uint8-p (swb27-l-idle-cpu index))
       (swb27-address-p (swb27-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb27-region base))))))

(defun swb27-linked-p ()
  (if (swb27-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun swb27-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swb27-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb27-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb27-address-base address))
    (<= 0 (swb27-address-offset address))
    (<=
     (+ (swb27-address-offset address) length)
     (swb27-allocation (swb27-address-base address))))))

(defun swb27-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb27-address-base address)))
    (<= 0 (swb27-address-offset address))
    (<=
     (+ (swb27-address-offset address) length)
     (swb27-allocation (swb27-address-base address))))))

(defun swb27-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb27-address-base left)
     (swb27-address-base right)))
   (<=
    (+ (swb27-address-offset right) right-length)
    (swb27-address-offset left))
   (<=
    (+ (swb27-address-offset left) left-length)
    (swb27-address-offset right))))

;; Exact unfolding of Memory.framed for t_5.

(defun-sk swb27-framed-p ()
  (forall (address)
    (implies
     (swb27-address-p address)
     (<=
      (swb27-region
       (swb27-address-base (swb27-t5 address)))
      0))))

;; Exact havoc_access values for the two source havoc expressions.

(defun swb27-havoc19-value
    (protected-start protected-length query)
  (if
      (swb27-separated-p
       query 1 protected-start protected-length)
      (swb27-t3 query)
    (swb27-t1 query)))

(defun swb27-havoc21-value
    (protected-start protected-length query)
  (if
      (swb27-separated-p
       query 1 protected-start protected-length)
      (swb27-t3 query)
    (swb27-t2 query)))

;; Exact unfolding of p_idle_core for t_5 and the havoced memory a_24.

(defun-sk swb27-havoc-idle-core-p (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb27-havoc21-value
         protected-start
         (swb27-l-size)
         (swb27-shift
          (swb27-t5
           (swb27-shift
            (swb27-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb27-l-size))
        (not
         (equal
          (swb27-l-idle-cpu index)
          0))))))))

;; Exact unfolding of p_idle_core for t_5 and the arbitrary integer memory
;; t_4 used in the nonzero branch.

(defun-sk swb27-t4-idle-core-p (cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb27-t4
         (swb27-shift
          (swb27-t5
           (swb27-shift
            (swb27-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb27-l-size))
        (not
         (equal
          (swb27-l-idle-cpu index)
          0))))))))

;; Function equality a_24 = t_4 is represented extensionally on the exact
;; address domain.

(defun-sk swb27-havoc21-equals-t4-p (protected-start)
  (forall (address)
    (implies
     (swb27-address-p address)
     (equal
      (swb27-havoc21-value
       protected-start
       (swb27-l-size)
       address)
      (swb27-t4 address)))))

;; The existential tail condition shared by four source hypotheses.

(defun-sk swb27-selected-tail-exists-p
    (protected-start a16 a6 x3)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swb27-havoc21-value
        protected-start
        (swb27-l-size)
        (swb27-shift a16 index))
       0))
     (not
      (equal
       (swb27-havoc21-value
        protected-start
        (swb27-l-size)
        (swb27-shift a6 index))
       0))
     (< index (swb27-l-size))
     (<= x3 index))))

;; When i_2 is -1, every selected position of a_20 maps to a selected
;; position of a_16.

(defun-sk swb27-a20-to-a16-p
    (protected-start a20 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb27-havoc21-value
         protected-start
         (swb27-l-size)
         (swb27-shift a20 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb27-l-size))
        (not
         (equal
          (swb27-havoc21-value
           protected-start
           (swb27-l-size)
           (swb27-shift a16 index))
          0))))))))

;; The universal no-pair condition from x_3 through l_size.

(defun-sk swb27-tail-zero-p
    (protected-start a16 a6 x3)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index (swb27-l-size))
      (implies
       (<= x3 index)
       (or
        (equal
         (swb27-havoc21-value
          protected-start
          (swb27-l-size)
          (swb27-shift a16 index))
         0)
        (equal
         (swb27-havoc21-value
          protected-start
          (swb27-l-size)
          (swb27-shift a6 index))
         0)))))))

;; The same no-pair condition below i_3.

(defun-sk swb27-prefix-zero-p
    (protected-start a16 a6 x3 i3)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index i3)
      (implies
       (<= x3 index)
       (or
        (equal
         (swb27-havoc21-value
          protected-start
          (swb27-l-size)
          (swb27-shift a16 index))
         0)
        (equal
         (swb27-havoc21-value
          protected-start
          (swb27-l-size)
          (swb27-shift a6 index))
         0)))))))

;; Every position selected by both a_6 and a_20 below the given bound has an
;; idle-CPU value of zero.

(defun-sk swb27-selected-prefix-idle-zero-p
    (protected-start a6 a20 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb27-havoc21-value
         protected-start
         (swb27-l-size)
         (swb27-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb27-havoc21-value
          protected-start
          (swb27-l-size)
          (swb27-shift a20 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index bound)
         (implies
          (< index (swb27-l-size))
          (equal
           (swb27-l-idle-cpu index)
           0)))))))))

;; Every position selected by both masks in [i_2, i_4) is not an idle core.

(defun-sk swb27-selected-range-not-idle-core-p
    (protected-start a6 a20 i2 i4)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb27-havoc21-value
         protected-start
         (swb27-l-size)
         (swb27-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb27-havoc21-value
          protected-start
          (swb27-l-size)
          (swb27-shift a20 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= i2 index)
         (implies
          (< index i4)
          (implies
           (< index (swb27-l-size))
           (not
            (swb27-havoc-idle-core-p
             protected-start index)))))))))))

;; A selected a_20 position has either a selected a_16 position or is not an
;; idle core.

(defun-sk swb27-a20-to-a16-or-not-idle-core-p
    (protected-start a20 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb27-havoc21-value
         protected-start
         (swb27-l-size)
         (swb27-shift a20 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb27-l-size))
        (or
         (not
          (equal
           (swb27-havoc21-value
            protected-start
            (swb27-l-size)
            (swb27-shift a16 index))
           0))
         (not
          (swb27-havoc-idle-core-p
           protected-start index)))))))))

;; Separation of a_18 from every pointed-to array mask.

(defun-sk swb27-a18-separated-p (a18 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb27-l-size))
       (swb27-separated-p
        a18
        (swb27-l-size)
        (swb27-shift
         (swb27-t5
          (swb27-shift
           (swb27-shift a index)
           0))
         0)
        (swb27-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb27-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((a28 (swb27-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb27-l-size))
         (and
          (swb27-valid-rd-p a28 1)
          (swb27-valid-rw-p
           (swb27-shift
            (swb27-t5
             (swb27-shift a28 0))
            0)
           (swb27-l-size)))))))))

;; The two a_19 mask views agree at every valid index.

(defun-sk swb27-havoc19-agreement-p
    (protected-start a20 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb27-l-size))
       (iff
        (not
         (equal
          (swb27-havoc19-value
           protected-start
           (swb27-l-size)
           (swb27-shift a20 index))
          0))
        (not
         (equal
          (swb27-havoc19-value
           protected-start
           (swb27-l-size)
           (swb27-shift a16 index))
          0))))))))

;; Every selected a_16 position is selected in a_20.

(defun-sk swb27-a16-to-a20-p
    (protected-start a16 a20)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb27-havoc21-value
         protected-start
         (swb27-l-size)
         (swb27-shift a16 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb27-l-size))
        (not
         (equal
          (swb27-havoc21-value
           protected-start
           (swb27-l-size)
           (swb27-shift a20 index))
          0))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb27-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb27-l-size))
       (swb27-separated-p
        mask
        (swb27-l-size)
        (swb27-shift
         (swb27-t5
          (swb27-shift
           (swb27-shift a index)
           0))
         0)
        (swb27-l-size)))))))

(defun-sk swb27-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb27-address-p address)
     (let*
         ((a29 (swb27-l-sched-group-cpus address))
          (a30
           (swb27-shift
            (swb27-t5
             (swb27-shift a29 0))
            0)))
       (and
        (swb27-valid-rd-p a29 1)
        (swb27-valid-rd-p a30 (swb27-l-size))
        (swb27-separated-from-array-masks-p a30 a))))))

(defun-sk swb27-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb27-address-p address)
     (let*
         ((a29 (swb27-l-sched-group-mask address))
          (a30
           (swb27-shift
            (swb27-t5
             (swb27-shift a29 0))
            0)))
       (and
        (swb27-valid-rd-p a29 1)
        (swb27-valid-rd-p a30 (swb27-l-size))
        (swb27-separated-from-array-masks-p a30 a))))))

(defun-sk swb27-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb27-address-p address)
     (let*
         ((a29 (swb27-l-group-balance-mask address))
          (a30
           (swb27-shift
            (swb27-t5
             (swb27-shift a29 0))
            0)))
       (and
        (swb27-valid-rd-p a29 1)
        (swb27-valid-rd-p a30 (swb27-l-size))
        (swb27-separated-from-array-masks-p a30 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb27-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((a28 (swb27-l-cpu-smt-mask index))
          (a29
           (swb27-shift
            (swb27-t5
             (swb27-shift a28 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb27-l-size))
         (and
          (swb27-valid-rd-p a28 1)
          (swb27-valid-rd-p a29 (swb27-l-size))
          (swb27-separated-from-array-masks-p a29 a))))))))

(defun swb27-goal-body
    (a1 a source-a2 i1 i3 i2 i4 i i5 p1 p)
  (implies
    (and
     (swb27-function-types-p)
     (swb27-scheduler-schema-types-p)
     (swb27-zero-mask-memory-instance-p)
     (swb27-q-mask-refl-p)
     (swb27-q-mask-symm-p)
     (swb27-q-mask-trans-p)
     (integerp (swb27-l-size))
     (< 0 (swb27-l-size))
     (<= (swb27-l-size) 2147483647)
     (swb27-address-p a1)
     (swb27-address-p a)
     (swb27-address-p source-a2)
     (integerp i1)
     (integerp i3)
     (integerp i2)
     (integerp i4)
     (integerp i)
     (integerp i5)
     (booleanp p1)
     (booleanp p))
    (let*
        ((a2 (swb27-shift a1 3))
         (x (swb27-t3 a2))
         (a3 (swb27-shift a1 4))
         (a4 (swb27-t5 a3))
         (a5 (swb27-shift a4 0))
         (a6 (swb27-t5 a5))
         (a7 (swb27-shift a1 1))
         (x1 (swb27-t3 a7))
         (x2 (swb27-t3 (swb27-shift a6 x1)))
         (a8 (swb27-shift a1 0))
         (a9 (swb27-shift a i1))
         (a10 (swb27-t5 a8))
         (a11 (swb27-shift a10 1))
         (a12 (swb27-shift a9 0))
         (a13 (swb27-shift a10 0))
         (a14 (swb27-t5 a13))
         (a15 (swb27-l-group-balance-mask a14))
         (a19 (swb27-shift source-a2 0))
         (a21
          (swb27-shift
           (swb27-t5 a19)
           1))
         (x4 (swb27-t4 a21))
         (a16 (swb27-t5 a12))
         (a17 (swb27-shift a16 0))
         (a18 (swb27-shift a6 0))
         (a20
          (swb27-t5
           (swb27-shift a15 0)))
         (a22
          (swb27-havoc21-value
           a17
           (swb27-l-size)
           (swb27-shift a16 i3)))
         (a23
          (swb27-havoc21-value
           a17
           (swb27-l-size)
           (swb27-shift a6 i2)))
         (a24
          (swb27-havoc21-value
           a17
           (swb27-l-size)
           (swb27-shift a6 i3)))
         (a25
          (swb27-havoc21-value
           a17
           (swb27-l-size)
           (swb27-shift a20 i2)))
         (a26
          (swb27-havoc21-value
           a17
           (swb27-l-size)
           a11))
         (a27 (swb27-shift a20 0))
         (x3 (swb27-to-uint32 i4)))
      (implies
       (and
        (iff
         (not (equal (swb27-l-idle-cpu i3) 0))
         (not (equal i 0)))
        (not (equal x 2))
        (not (equal x2 0))
        (<= 0 i1)
        (< i1 (swb27-l-size))
        (<= 0 i3)
        (< i3 (swb27-l-size))
        (<= 0 i4)
        (<= i4 (swb27-l-size))
        (< (swb27-to-uint32 i3) (swb27-l-size))
        (<= 0 x1)
        (< x1 (swb27-l-size))
        (<= (swb27-region (swb27-address-base a)) 0)
        (<= (swb27-region (swb27-address-base a1)) 0)
        (swb27-framed-p)
        (swb27-linked-p)
        (swb27-is-uint8-p i)
        (swb27-is-uint32-p i1)
        (swb27-is-sint32-p i2)
        (swb27-is-sint32-p i5)
        (swb27-is-sint32-p i3)
        (swb27-is-sint32-p i4)
        (swb27-valid-rd-p a1 5)
        (swb27-is-uint32-p x)
        (swb27-is-sint32-p x1)
        (swb27-valid-rd-p a3 1)
        (swb27-valid-rd-p a7 1)
        (swb27-valid-rd-p a2 1)
        (swb27-valid-rd-p a8 1)
        (swb27-valid-rd-p a9 1)
        (swb27-valid-rd-p a4 1)
        (swb27-valid-rd-p
         (swb27-t5 (swb27-shift a1 2))
         2)
        (swb27-valid-rd-p a10 2)
        (swb27-is-sint32-p (swb27-t3 a11))
        (swb27-is-sint32-p x4)
        (swb27-valid-rd-p a12 1)
        (swb27-valid-rd-p a5 1)
        (swb27-valid-rd-p a13 1)
        (swb27-valid-rd-p a14 1)
        (swb27-valid-rd-p a15 1)
        (swb27-is-uint8-p x2)
        (swb27-valid-rd-p a17 (swb27-l-size))
        (swb27-valid-rd-p a18 (swb27-l-size))
        (swb27-valid-rw-p a17 (swb27-l-size))
        (swb27-is-uint8-p
         (swb27-havoc19-value
          a17
          (swb27-l-size)
          (swb27-shift a6 -1)))
        (swb27-is-uint8-p
         (swb27-havoc19-value
          a17
          (swb27-l-size)
          (swb27-shift a20 -1)))
        (swb27-is-uint8-p a22)
        (swb27-is-uint8-p a23)
        (swb27-is-uint8-p a24)
        (swb27-is-uint8-p a25)
        (swb27-is-sint32-p
         (swb27-havoc19-value
          a17
          (swb27-l-size)
          a11))
        (swb27-is-sint32-p a26)
        (swb27-valid-rd-p a27 (swb27-l-size))
        (swb27-separated-p
         a17
         (swb27-l-size)
         a27
         (swb27-l-size))
        (if
            (equal i 0)
            (and
             (not p1)
             (equal i3 i5))
          (and
           (not p)
           p1
           (equal source-a2 a1)
           (not (equal (swb27-l-idle-cpu i3) 0))
           (equal (swb27-land 7 x4) 0)
           (swb27-havoc21-equals-t4-p a17)
           (not (swb27-t4-idle-core-p i3))
           (swb27-valid-rd-p a19 1)
           (swb27-valid-rd-p a21 1)))
        (implies
         (not
          (equal
           (swb27-land 7 a26)
           0))
         (equal i2 -1))
        (implies
         (not (equal i2 -1))
         (and
          (not (equal (swb27-l-idle-cpu i2) 0))
          (not (equal a23 0))
          (not (equal a25 0))
          (<= 0 i2)
          (< i2 (swb27-l-size))))
        (implies
         (equal i2 -1)
         (swb27-a20-to-a16-p a17 a20 a16))
        (implies
         (swb27-selected-tail-exists-p
          a17 a16 a6 x3)
         (<= x3 i3))
        (implies
         (swb27-selected-tail-exists-p
          a17 a16 a6 x3)
         (and
          (not (equal a22 0))
          (not (equal a24 0))))
        (implies
         (swb27-tail-zero-p a17 a16 a6 x3)
         (equal (swb27-l-size) i3))
        (implies
         (not (equal i2 -1))
         (swb27-selected-prefix-idle-zero-p
          a17 a6 a20 i2))
        (implies
         (equal i2 -1)
         (swb27-selected-prefix-idle-zero-p
          a17 a6 a20 i4))
        (implies
         (swb27-selected-tail-exists-p
          a17 a16 a6 x3)
         (swb27-prefix-zero-p
          a17 a16 a6 x3 i3))
        (implies
         (not (equal i2 -1))
         (swb27-selected-range-not-idle-core-p
          a17 a6 a20 i2 i4))
        (implies
         (not (equal i2 -1))
         (swb27-a20-to-a16-or-not-idle-core-p
          a17 a20 a16))
        (swb27-a18-separated-p a18 a)
        (swb27-array-layout-p a)
        (swb27-havoc19-agreement-p a17 a20 a16)
        (swb27-a16-to-a20-p a17 a16 a20)
        (swb27-sched-group-cpus-layout-p a)
        (swb27-sched-group-mask-layout-p a)
        (swb27-group-balance-mask-layout-p a)
        (swb27-cpu-smt-layout-p a)
        (or
         (equal i 0)
         (equal i 1)))
       (if p1
           (<= i3 2147483646)
         (<= i5 2147483646))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-signed-overflow-goal27-statement ()
  (forall
   (a1 a source-a2 i1 i3 i2 i4 i i5 p1 p)
   (swb27-goal-body
    a1 a source-a2 i1 i3 i2 i4 i i5 p1 p)))

(value-triple :itpeval-statement-checked)

:q
