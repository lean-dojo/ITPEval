;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_14_goal25:
;; readability of the second scheduling-structure field under the stated
;; integer ranges, memory validity, framing, separation, havoc, CPU-mask
;; layout, and quantified scheduling hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb25-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb25-address-base (address)
  (car address))

(defun swb25-address-offset (address)
  (cdr address))

(defun swb25-shift (address amount)
  (cons
   (swb25-address-base address)
   (+ (swb25-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memory functions t_1,
;; t_2, t_3, t_4, allocation map t, and the fixed source symbols.

(defstub swb25-t1 (address) t)
(defstub swb25-t2 (address) t)
(defstub swb25-t3 (address) t)
(defstub swb25-t4 (address) t)
(defstub swb25-allocation (index) t)
(defstub swb25-region (base) t)
(defstub swb25-linked-op () t)
(defstub swb25-l-size () t)
(defstub swb25-mask-memory-apply (memory-symbol address) t)
(defstub swb25-mask-pointer-apply (pointer-symbol address) t)
(defstub swb25-l-idle-cpu (index) t)
(defstub swb25-l-sched-group-cpus (address) t)
(defstub swb25-l-sched-group-mask (address) t)
(defstub swb25-l-group-balance-mask (address) t)
(defstub swb25-l-cpu-smt-mask (index) t)

(defun swb25-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb25-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb25-address-p address)
      (and
       (integerp
        (swb25-mask-memory-apply
         memory-symbol address))
       (swb25-address-p
        (swb25-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb25-is-uint8-p
        (swb25-l-idle-cpu index))
       (swb25-address-p
        (swb25-l-cpu-smt-mask index)))))))

(defun-sk swb25-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb25-address-p address)
     (equal
      (swb25-mask-memory-apply
       'swb25-zero-memory address)
      0))))

(defun-sk swb25-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb25-l-size)))
     (not
      (equal
       (swb25-mask-memory-apply
        memory-symbol
        (swb25-shift
         (swb25-mask-pointer-apply
          pointer-symbol
          (swb25-shift
           (swb25-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb25-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb25-mask-memory-apply
         memory-symbol
         (swb25-shift
          (swb25-mask-pointer-apply
           pointer-symbol
           (swb25-shift
            (swb25-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb25-l-size))
      (<= 0 j)
      (< j (swb25-l-size)))
     (not
      (equal
       (swb25-mask-memory-apply
        memory-symbol
        (swb25-shift
         (swb25-mask-pointer-apply
          pointer-symbol
          (swb25-shift
           (swb25-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb25-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb25-mask-memory-apply
         memory-symbol
         (swb25-shift
          (swb25-mask-pointer-apply
           pointer-symbol
           (swb25-shift
            (swb25-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb25-mask-memory-apply
         memory-symbol
         (swb25-shift
          (swb25-mask-pointer-apply
           pointer-symbol
           (swb25-shift
            (swb25-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb25-l-size))
      (<= 0 j)
      (< j (swb25-l-size))
      (<= 0 k)
      (< k (swb25-l-size)))
     (not
      (equal
       (swb25-mask-memory-apply
        memory-symbol
        (swb25-shift
         (swb25-mask-pointer-apply
          pointer-symbol
          (swb25-shift
           (swb25-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb25-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb25-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun-sk swb25-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb25-address-p address)
      (and
       (integerp (swb25-t1 address))
       (integerp (swb25-t2 address))
       (integerp (swb25-t3 address))
       (swb25-address-p (swb25-t4 address))
       (swb25-address-p
        (swb25-l-sched-group-cpus address))
       (swb25-address-p
        (swb25-l-sched-group-mask address))
       (swb25-address-p
        (swb25-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb25-allocation index))
       (swb25-is-uint8-p (swb25-l-idle-cpu index))
       (swb25-address-p (swb25-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb25-region base))))))

(defun swb25-linked-p ()
  (if (swb25-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun swb25-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swb25-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb25-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb25-address-base address))
    (<= 0 (swb25-address-offset address))
    (<=
     (+ (swb25-address-offset address) length)
     (swb25-allocation (swb25-address-base address))))))

(defun swb25-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb25-address-base address)))
    (<= 0 (swb25-address-offset address))
    (<=
     (+ (swb25-address-offset address) length)
     (swb25-allocation (swb25-address-base address))))))

(defun swb25-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb25-address-base left)
     (swb25-address-base right)))
   (<=
    (+ (swb25-address-offset right) right-length)
    (swb25-address-offset left))
   (<=
    (+ (swb25-address-offset left) left-length)
    (swb25-address-offset right))))

;; Exact unfolding of Memory.framed for t_4.

(defun-sk swb25-framed-p ()
  (forall (address)
    (implies
     (swb25-address-p address)
     (<=
      (swb25-region
       (swb25-address-base (swb25-t4 address)))
      0))))

;; Exact havoc_access values for the two source havoc expressions.

(defun swb25-havoc19-value
    (protected-start protected-length query)
  (if
      (swb25-separated-p
       query 1 protected-start protected-length)
      (swb25-t3 query)
    (swb25-t1 query)))

(defun swb25-havoc21-value
    (protected-start protected-length query)
  (if
      (swb25-separated-p
       query 1 protected-start protected-length)
      (swb25-t3 query)
    (swb25-t2 query)))

;; Exact unfolding of p_idle_core for t_4 and the havoced memory a_21.

(defun-sk swb25-idle-core-p (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb25-havoc21-value
         protected-start
         (swb25-l-size)
         (swb25-shift
          (swb25-t4
           (swb25-shift
            (swb25-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb25-l-size))
        (not
         (equal
          (swb25-l-idle-cpu index)
          0))))))))

;; The existential tail condition shared by four source hypotheses.

(defun-sk swb25-selected-tail-exists-p
    (protected-start a16 a6 x3)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swb25-havoc21-value
        protected-start
        (swb25-l-size)
        (swb25-shift a16 index))
       0))
     (not
      (equal
       (swb25-havoc21-value
        protected-start
        (swb25-l-size)
        (swb25-shift a6 index))
       0))
     (< index (swb25-l-size))
     (<= x3 index))))

;; When i_2 is -1, every selected position of a_20 maps to a selected
;; position of a_16.

(defun-sk swb25-a20-to-a16-p
    (protected-start a20 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb25-havoc21-value
         protected-start
         (swb25-l-size)
         (swb25-shift a20 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb25-l-size))
        (not
         (equal
          (swb25-havoc21-value
           protected-start
           (swb25-l-size)
           (swb25-shift a16 index))
          0))))))))

;; The universal no-pair condition from x_3 through l_size.

(defun-sk swb25-tail-zero-p
    (protected-start a16 a6 x3)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index (swb25-l-size))
      (implies
       (<= x3 index)
       (or
        (equal
         (swb25-havoc21-value
          protected-start
          (swb25-l-size)
          (swb25-shift a16 index))
         0)
        (equal
         (swb25-havoc21-value
          protected-start
          (swb25-l-size)
          (swb25-shift a6 index))
         0)))))))

;; The same no-pair condition below i_3.

(defun-sk swb25-prefix-zero-p
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
         (swb25-havoc21-value
          protected-start
          (swb25-l-size)
          (swb25-shift a16 index))
         0)
        (equal
         (swb25-havoc21-value
          protected-start
          (swb25-l-size)
          (swb25-shift a6 index))
         0)))))))

;; Every position selected by both a_6 and a_20 below the given bound has an
;; idle-CPU value of zero.

(defun-sk swb25-selected-prefix-idle-zero-p
    (protected-start a6 a20 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb25-havoc21-value
         protected-start
         (swb25-l-size)
         (swb25-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb25-havoc21-value
          protected-start
          (swb25-l-size)
          (swb25-shift a20 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index bound)
         (implies
          (< index (swb25-l-size))
          (equal
           (swb25-l-idle-cpu index)
           0)))))))))

;; Every position selected by both masks in [i_2, i_4) is not an idle core.

(defun-sk swb25-selected-range-not-idle-core-p
    (protected-start a6 a20 i2 i4)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb25-havoc21-value
         protected-start
         (swb25-l-size)
         (swb25-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb25-havoc21-value
          protected-start
          (swb25-l-size)
          (swb25-shift a20 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= i2 index)
         (implies
          (< index i4)
          (implies
           (< index (swb25-l-size))
           (not
            (swb25-idle-core-p
             protected-start index)))))))))))

;; A selected a_20 position has either a selected a_16 position or is not an
;; idle core.

(defun-sk swb25-a20-to-a16-or-not-idle-core-p
    (protected-start a20 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb25-havoc21-value
         protected-start
         (swb25-l-size)
         (swb25-shift a20 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb25-l-size))
        (or
         (not
          (equal
           (swb25-havoc21-value
            protected-start
            (swb25-l-size)
            (swb25-shift a16 index))
           0))
         (not
          (swb25-idle-core-p
           protected-start index)))))))))

;; Separation of a_18 from every pointed-to array mask.

(defun-sk swb25-a18-separated-p (a18 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb25-l-size))
       (swb25-separated-p
        a18
        (swb25-l-size)
        (swb25-shift
         (swb25-t4
          (swb25-shift
           (swb25-shift a index)
           0))
         0)
        (swb25-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb25-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((a28 (swb25-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb25-l-size))
         (and
          (swb25-valid-rd-p a28 1)
          (swb25-valid-rw-p
           (swb25-shift
            (swb25-t4
             (swb25-shift a28 0))
            0)
           (swb25-l-size)))))))))

;; The two a_19 mask views agree at every valid index.

(defun-sk swb25-havoc19-agreement-p
    (protected-start a20 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb25-l-size))
       (iff
        (not
         (equal
          (swb25-havoc19-value
           protected-start
           (swb25-l-size)
           (swb25-shift a20 index))
          0))
        (not
         (equal
          (swb25-havoc19-value
           protected-start
           (swb25-l-size)
           (swb25-shift a16 index))
          0))))))))

;; Every selected a_16 position is selected in a_20.

(defun-sk swb25-a16-to-a20-p
    (protected-start a16 a20)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb25-havoc21-value
         protected-start
         (swb25-l-size)
         (swb25-shift a16 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb25-l-size))
        (not
         (equal
          (swb25-havoc21-value
           protected-start
           (swb25-l-size)
           (swb25-shift a20 index))
          0))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb25-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb25-l-size))
       (swb25-separated-p
        mask
        (swb25-l-size)
        (swb25-shift
         (swb25-t4
          (swb25-shift
           (swb25-shift a index)
           0))
         0)
        (swb25-l-size)))))))

(defun-sk swb25-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb25-address-p address)
     (let*
         ((a29 (swb25-l-sched-group-cpus address))
          (a30
           (swb25-shift
            (swb25-t4
             (swb25-shift a29 0))
            0)))
       (and
        (swb25-valid-rd-p a29 1)
        (swb25-valid-rd-p a30 (swb25-l-size))
        (swb25-separated-from-array-masks-p a30 a))))))

(defun-sk swb25-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb25-address-p address)
     (let*
         ((a29 (swb25-l-sched-group-mask address))
          (a30
           (swb25-shift
            (swb25-t4
             (swb25-shift a29 0))
            0)))
       (and
        (swb25-valid-rd-p a29 1)
        (swb25-valid-rd-p a30 (swb25-l-size))
        (swb25-separated-from-array-masks-p a30 a))))))

(defun-sk swb25-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb25-address-p address)
     (let*
         ((a29 (swb25-l-group-balance-mask address))
          (a30
           (swb25-shift
            (swb25-t4
             (swb25-shift a29 0))
            0)))
       (and
        (swb25-valid-rd-p a29 1)
        (swb25-valid-rd-p a30 (swb25-l-size))
        (swb25-separated-from-array-masks-p a30 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb25-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((a28 (swb25-l-cpu-smt-mask index))
          (a29
           (swb25-shift
            (swb25-t4
             (swb25-shift a28 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb25-l-size))
         (and
          (swb25-valid-rd-p a28 1)
          (swb25-valid-rd-p a29 (swb25-l-size))
          (swb25-separated-from-array-masks-p a29 a))))))))

(defun swb25-goal-body (a1 a i1 i3 i2 i4)
  (implies
    (and
     (swb25-function-types-p)
     (swb25-scheduler-schema-types-p)
     (swb25-zero-mask-memory-instance-p)
     (swb25-q-mask-refl-p)
     (swb25-q-mask-symm-p)
     (swb25-q-mask-trans-p)
     (integerp (swb25-l-size))
     (< 0 (swb25-l-size))
     (<= (swb25-l-size) 2147483647)
     (swb25-address-p a1)
     (swb25-address-p a)
     (integerp i1)
     (integerp i3)
     (integerp i2)
     (integerp i4))
    (let*
        ((a2 (swb25-shift a1 3))
         (x (swb25-t3 a2))
         (a3 (swb25-shift a1 4))
         (a4 (swb25-t4 a3))
         (a5 (swb25-shift a4 0))
         (a6 (swb25-t4 a5))
         (a7 (swb25-shift a1 1))
         (x1 (swb25-t3 a7))
         (x2 (swb25-t3 (swb25-shift a6 x1)))
         (a8 (swb25-shift a1 0))
         (a9 (swb25-shift a i1))
         (a10 (swb25-t4 a8))
         (a11 (swb25-shift a10 1))
         (a12 (swb25-shift a9 0))
         (a13 (swb25-shift a10 0))
         (a14 (swb25-t4 a13))
         (a15 (swb25-l-group-balance-mask a14))
         (a16 (swb25-t4 a12))
         (a17 (swb25-shift a16 0))
         (a18 (swb25-shift a6 0))
         (a20
          (swb25-t4
           (swb25-shift a15 0)))
         (a22
          (swb25-havoc21-value
           a17
           (swb25-l-size)
           (swb25-shift a16 i3)))
         (a23
          (swb25-havoc21-value
           a17
           (swb25-l-size)
           (swb25-shift a6 i2)))
         (a24
          (swb25-havoc21-value
           a17
           (swb25-l-size)
           (swb25-shift a6 i3)))
         (a25
          (swb25-havoc21-value
           a17
           (swb25-l-size)
           (swb25-shift a20 i2)))
         (a26
          (swb25-havoc21-value
           a17
           (swb25-l-size)
           a11))
         (a27 (swb25-shift a20 0))
         (x3 (swb25-to-uint32 i4)))
      (implies
       (and
        (not (equal (swb25-l-idle-cpu i3) 0))
        (not (equal x 2))
        (not (equal x2 0))
        (<= 0 i1)
        (< i1 (swb25-l-size))
        (<= 0 i3)
        (< i3 (swb25-l-size))
        (<= 0 i4)
        (<= i4 (swb25-l-size))
        (< (swb25-to-uint32 i3) (swb25-l-size))
        (<= 0 x1)
        (< x1 (swb25-l-size))
        (<= (swb25-region (swb25-address-base a)) 0)
        (<= (swb25-region (swb25-address-base a1)) 0)
        (swb25-framed-p)
        (swb25-linked-p)
        (swb25-is-uint32-p i1)
        (swb25-is-sint32-p i2)
        (swb25-is-sint32-p i3)
        (swb25-is-sint32-p i4)
        (swb25-valid-rd-p a1 5)
        (swb25-is-uint32-p x)
        (swb25-is-sint32-p x1)
        (swb25-valid-rd-p a3 1)
        (swb25-valid-rd-p a7 1)
        (swb25-valid-rd-p a2 1)
        (swb25-valid-rd-p a8 1)
        (swb25-valid-rd-p a9 1)
        (swb25-valid-rd-p a4 1)
        (swb25-valid-rd-p
         (swb25-t4 (swb25-shift a1 2))
         2)
        (swb25-valid-rd-p a10 2)
        (swb25-is-sint32-p (swb25-t3 a11))
        (swb25-valid-rd-p a12 1)
        (swb25-valid-rd-p a5 1)
        (swb25-valid-rd-p a13 1)
        (swb25-valid-rd-p a14 1)
        (swb25-valid-rd-p a15 1)
        (swb25-is-uint8-p x2)
        (swb25-valid-rd-p a17 (swb25-l-size))
        (swb25-valid-rd-p a18 (swb25-l-size))
        (swb25-valid-rw-p a17 (swb25-l-size))
        (swb25-is-uint8-p
         (swb25-havoc19-value
          a17
          (swb25-l-size)
          (swb25-shift a6 -1)))
        (swb25-is-uint8-p
         (swb25-havoc19-value
          a17
          (swb25-l-size)
          (swb25-shift a20 -1)))
        (swb25-is-uint8-p a22)
        (swb25-is-uint8-p a23)
        (swb25-is-uint8-p a24)
        (swb25-is-uint8-p a25)
        (swb25-is-sint32-p
         (swb25-havoc19-value
          a17
          (swb25-l-size)
          a11))
        (swb25-is-sint32-p a26)
        (swb25-valid-rd-p a27 (swb25-l-size))
        (swb25-separated-p
         a17
         (swb25-l-size)
         a27
         (swb25-l-size))
        (implies
         (not
          (equal
           (swb25-land 7 a26)
           0))
         (equal i2 -1))
        (implies
         (not (equal i2 -1))
         (and
          (not (equal (swb25-l-idle-cpu i2) 0))
          (not (equal a23 0))
          (not (equal a25 0))
          (<= 0 i2)
          (< i2 (swb25-l-size))))
        (implies
         (equal i2 -1)
         (swb25-a20-to-a16-p a17 a20 a16))
        (implies
         (swb25-selected-tail-exists-p
          a17 a16 a6 x3)
         (<= x3 i3))
        (implies
         (swb25-selected-tail-exists-p
          a17 a16 a6 x3)
         (and
          (not (equal a22 0))
          (not (equal a24 0))))
        (implies
         (swb25-tail-zero-p a17 a16 a6 x3)
         (equal (swb25-l-size) i3))
        (implies
         (not (equal i2 -1))
         (swb25-selected-prefix-idle-zero-p
          a17 a6 a20 i2))
        (implies
         (equal i2 -1)
         (swb25-selected-prefix-idle-zero-p
          a17 a6 a20 i4))
        (implies
         (swb25-selected-tail-exists-p
          a17 a16 a6 x3)
         (swb25-prefix-zero-p
          a17 a16 a6 x3 i3))
        (implies
         (not (equal i2 -1))
         (swb25-selected-range-not-idle-core-p
          a17 a6 a20 i2 i4))
        (implies
         (not (equal i2 -1))
         (swb25-a20-to-a16-or-not-idle-core-p
          a17 a20 a16))
        (swb25-a18-separated-p a18 a)
        (swb25-array-layout-p a)
        (swb25-havoc19-agreement-p a17 a20 a16)
        (swb25-a16-to-a20-p a17 a16 a20)
        (swb25-sched-group-cpus-layout-p a)
        (swb25-sched-group-mask-layout-p a)
        (swb25-group-balance-mask-layout-p a)
        (swb25-cpu-smt-layout-p a))
       (swb25-valid-rd-p a11 1)))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-14-goal25-statement ()
  (forall
   (a1 a i1 i3 i2 i4)
   (swb25-goal-body a1 a i1 i3 i2 i4)))

(value-triple :itpeval-statement-checked)

:q
