;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_call_find_next_and_bit_pre_2_goal32:
;; readability of the havoc-updated CPU mask passed to find_next_and_bit,
;; under the stated integer bounds, memory validity, framing, separation,
;; bit-mask, scheduling, and CPU-mask layout hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb32-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb32-address-base (address)
  (car address))

(defun swb32-address-offset (address)
  (cdr address))

(defun swb32-shift (address amount)
  (cons
   (swb32-address-base address)
   (+ (swb32-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memory functions t_1,
;; t_2, t_3, t_4, allocation map t, and the fixed source symbols.

(defstub swb32-t1 (address) t)
(defstub swb32-t2 (address) t)
(defstub swb32-t3 (address) t)
(defstub swb32-t4 (address) t)
(defstub swb32-allocation (index) t)
(defstub swb32-region (base) t)
(defstub swb32-linked-op () t)
(defstub swb32-l-size () t)
(defstub swb32-mask-memory-apply (memory-symbol address) t)
(defstub swb32-mask-pointer-apply (pointer-symbol address) t)
(defstub swb32-l-idle-cpu (index) t)
(defstub swb32-l-sched-group-cpus (address) t)
(defstub swb32-l-sched-group-mask (address) t)
(defstub swb32-l-group-balance-mask (address) t)
(defstub swb32-l-cpu-smt-mask (index) t)

(defun swb32-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb32-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb32-address-p address)
      (and
       (integerp
        (swb32-mask-memory-apply
         memory-symbol address))
       (swb32-address-p
        (swb32-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb32-is-uint8-p
        (swb32-l-idle-cpu index))
       (swb32-address-p
        (swb32-l-cpu-smt-mask index)))))))

(defun-sk swb32-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb32-address-p address)
     (equal
      (swb32-mask-memory-apply
       'swb32-zero-memory address)
      0))))

(defun-sk swb32-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb32-l-size)))
     (not
      (equal
       (swb32-mask-memory-apply
        memory-symbol
        (swb32-shift
         (swb32-mask-pointer-apply
          pointer-symbol
          (swb32-shift
           (swb32-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb32-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb32-mask-memory-apply
         memory-symbol
         (swb32-shift
          (swb32-mask-pointer-apply
           pointer-symbol
           (swb32-shift
            (swb32-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb32-l-size))
      (<= 0 j)
      (< j (swb32-l-size)))
     (not
      (equal
       (swb32-mask-memory-apply
        memory-symbol
        (swb32-shift
         (swb32-mask-pointer-apply
          pointer-symbol
          (swb32-shift
           (swb32-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb32-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb32-mask-memory-apply
         memory-symbol
         (swb32-shift
          (swb32-mask-pointer-apply
           pointer-symbol
           (swb32-shift
            (swb32-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb32-mask-memory-apply
         memory-symbol
         (swb32-shift
          (swb32-mask-pointer-apply
           pointer-symbol
           (swb32-shift
            (swb32-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb32-l-size))
      (<= 0 j)
      (< j (swb32-l-size))
      (<= 0 k)
      (< k (swb32-l-size)))
     (not
      (equal
       (swb32-mask-memory-apply
        memory-symbol
        (swb32-shift
         (swb32-mask-pointer-apply
          pointer-symbol
          (swb32-shift
           (swb32-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb32-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb32-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are exactly the source function types over the full unbounded
;; integer and address domains.

(defun-sk swb32-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb32-address-p address)
      (and
       (integerp (swb32-t1 address))
       (integerp (swb32-t2 address))
       (integerp (swb32-t3 address))
       (swb32-address-p (swb32-t4 address))
       (swb32-address-p
        (swb32-l-sched-group-cpus address))
       (swb32-address-p
        (swb32-l-sched-group-mask address))
       (swb32-address-p
        (swb32-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb32-allocation index))
       (swb32-is-uint8-p (swb32-l-idle-cpu index))
       (swb32-address-p (swb32-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb32-region base))))))

(defun swb32-linked-p ()
  (if (swb32-linked-op) t nil))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swb32-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb32-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb32-address-base address))
    (<= 0 (swb32-address-offset address))
    (<=
     (+ (swb32-address-offset address) length)
     (swb32-allocation (swb32-address-base address))))))

(defun swb32-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb32-address-base address)))
    (<= 0 (swb32-address-offset address))
    (<=
     (+ (swb32-address-offset address) length)
     (swb32-allocation (swb32-address-base address))))))

(defun swb32-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb32-address-base left)
     (swb32-address-base right)))
   (<=
    (+ (swb32-address-offset right) right-length)
    (swb32-address-offset left))
   (<=
    (+ (swb32-address-offset left) left-length)
    (swb32-address-offset right))))

;; Exact unfolding of Memory.framed for t_4.

(defun-sk swb32-framed-p ()
  (forall (address)
    (implies
     (swb32-address-p address)
     (<=
      (swb32-region
       (swb32-address-base (swb32-t4 address)))
      0))))

;; Exact havoc_access values for the two source havoc expressions.

(defun swb32-havoc19-value
    (protected-start protected-length query)
  (if
      (swb32-separated-p
       query 1 protected-start protected-length)
      (swb32-t3 query)
    (swb32-t1 query)))

(defun swb32-havoc21-value
    (protected-start protected-length query)
  (if
      (swb32-separated-p
       query 1 protected-start protected-length)
      (swb32-t3 query)
    (swb32-t2 query)))

;; Exact unfolding of p_idle_core for t_4 and the havoced memory a_21.

(defun-sk swb32-idle-core-p (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb32-havoc21-value
         protected-start
         (swb32-l-size)
         (swb32-shift
          (swb32-t4
           (swb32-shift
            (swb32-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb32-l-size))
        (not
         (equal
          (swb32-l-idle-cpu index)
          0))))))))

;; When i_1 is -1, each selected a_20 position is also selected in a_17.

(defun-sk swb32-a20-to-a17-p
    (protected-start a20 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb32-havoc21-value
         protected-start
         (swb32-l-size)
         (swb32-shift a20 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb32-l-size))
        (not
         (equal
          (swb32-havoc21-value
           protected-start
           (swb32-l-size)
           (swb32-shift a17 index))
          0))))))))

;; Every position selected by both a_6 and a_20 below BOUND has idle value
;; zero.

(defun-sk swb32-selected-prefix-idle-zero-p
    (protected-start a6 a20 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb32-havoc21-value
         protected-start
         (swb32-l-size)
         (swb32-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb32-havoc21-value
          protected-start
          (swb32-l-size)
          (swb32-shift a20 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index bound)
         (implies
          (< index (swb32-l-size))
          (equal
           (swb32-l-idle-cpu index)
           0)))))))))

;; Every position selected by both masks in [LOWER, UPPER) is not an idle
;; core.

(defun-sk swb32-selected-range-not-idle-core-p
    (protected-start a6 a20 lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb32-havoc21-value
         protected-start
         (swb32-l-size)
         (swb32-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb32-havoc21-value
          protected-start
          (swb32-l-size)
          (swb32-shift a20 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= lower index)
         (implies
          (< index upper)
          (implies
           (< index (swb32-l-size))
           (not
            (swb32-idle-core-p
             protected-start index)))))))))))

;; A selected a_20 position has either a selected a_17 position or is not an
;; idle core.

(defun-sk swb32-a20-to-a17-or-not-idle-core-p
    (protected-start a20 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb32-havoc21-value
         protected-start
         (swb32-l-size)
         (swb32-shift a20 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb32-l-size))
        (or
         (not
          (equal
           (swb32-havoc21-value
            protected-start
            (swb32-l-size)
            (swb32-shift a17 index))
           0))
         (not
          (swb32-idle-core-p
           protected-start index)))))))))

;; Separation of a_16 from every pointed-to array mask.

(defun-sk swb32-a16-separated-p (a16 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb32-l-size))
       (swb32-separated-p
        a16
        (swb32-l-size)
        (swb32-shift
         (swb32-t4
          (swb32-shift
           (swb32-shift a index)
           0))
         0)
        (swb32-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb32-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((a26 (swb32-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb32-l-size))
         (and
          (swb32-valid-rd-p a26 1)
          (swb32-valid-rw-p
           (swb32-shift
            (swb32-t4
             (swb32-shift a26 0))
            0)
           (swb32-l-size)))))))))

;; The two a_19 mask views agree at every valid index.

(defun-sk swb32-havoc19-agreement-p
    (protected-start a20 a17)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb32-l-size))
       (iff
        (not
         (equal
          (swb32-havoc19-value
           protected-start
           (swb32-l-size)
           (swb32-shift a20 index))
          0))
        (not
         (equal
          (swb32-havoc19-value
           protected-start
           (swb32-l-size)
           (swb32-shift a17 index))
          0))))))))

;; Every selected a_17 position is selected in a_20.

(defun-sk swb32-a17-to-a20-p
    (protected-start a17 a20)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb32-havoc21-value
         protected-start
         (swb32-l-size)
         (swb32-shift a17 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb32-l-size))
        (not
         (equal
          (swb32-havoc21-value
           protected-start
           (swb32-l-size)
           (swb32-shift a20 index))
          0))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb32-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb32-l-size))
       (swb32-separated-p
        mask
        (swb32-l-size)
        (swb32-shift
         (swb32-t4
          (swb32-shift
           (swb32-shift a index)
           0))
         0)
        (swb32-l-size)))))))

(defun-sk swb32-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb32-address-p address)
     (let*
         ((a27 (swb32-l-sched-group-cpus address))
          (a28
           (swb32-shift
            (swb32-t4
             (swb32-shift a27 0))
            0)))
       (and
        (swb32-valid-rd-p a27 1)
        (swb32-valid-rd-p a28 (swb32-l-size))
        (swb32-separated-from-array-masks-p a28 a))))))

(defun-sk swb32-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb32-address-p address)
     (let*
         ((a27 (swb32-l-sched-group-mask address))
          (a28
           (swb32-shift
            (swb32-t4
             (swb32-shift a27 0))
            0)))
       (and
        (swb32-valid-rd-p a27 1)
        (swb32-valid-rd-p a28 (swb32-l-size))
        (swb32-separated-from-array-masks-p a28 a))))))

(defun-sk swb32-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb32-address-p address)
     (let*
         ((a27 (swb32-l-group-balance-mask address))
          (a28
           (swb32-shift
            (swb32-t4
             (swb32-shift a27 0))
            0)))
       (and
        (swb32-valid-rd-p a27 1)
        (swb32-valid-rd-p a28 (swb32-l-size))
        (swb32-separated-from-array-masks-p a28 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb32-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((a26 (swb32-l-cpu-smt-mask index))
          (a27
           (swb32-shift
            (swb32-t4
             (swb32-shift a26 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb32-l-size))
         (and
          (swb32-valid-rd-p a26 1)
          (swb32-valid-rd-p a27 (swb32-l-size))
          (swb32-separated-from-array-masks-p a27 a))))))))

(defun swb32-goal-body (a1 a i i1 i2)
  (implies
   (and
    (swb32-function-types-p)
    (swb32-scheduler-schema-types-p)
    (swb32-zero-mask-memory-instance-p)
    (swb32-q-mask-refl-p)
    (swb32-q-mask-symm-p)
    (swb32-q-mask-trans-p)
    (integerp (swb32-l-size))
    (< 0 (swb32-l-size))
    (<= (swb32-l-size) 2147483647)
    (swb32-address-p a1)
    (swb32-address-p a)
    (integerp i)
    (integerp i1)
    (integerp i2))
   (let*
       ((a2 (swb32-shift a1 3))
        (x (swb32-t3 a2))
        (a3 (swb32-shift a1 4))
        (a4 (swb32-t4 a3))
        (a5 (swb32-shift a4 0))
        (a6 (swb32-t4 a5))
        (a7 (swb32-shift a1 1))
        (x1 (swb32-t3 a7))
        (x2 (swb32-t3 (swb32-shift a6 x1)))
        (a8 (swb32-shift a1 0))
        (a9 (swb32-shift a i))
        (a10 (swb32-t4 a8))
        (a11 (swb32-shift a10 1))
        (a12 (swb32-shift a9 0))
        (a13 (swb32-shift a10 0))
        (a14 (swb32-t4 a13))
        (a15 (swb32-l-group-balance-mask a14))
        (a16 (swb32-shift a6 0))
        (a17 (swb32-t4 a12))
        (a18 (swb32-shift a17 0))
        (a20
         (swb32-t4
          (swb32-shift a15 0)))
        (a22
         (swb32-havoc21-value
          a18
          (swb32-l-size)
          (swb32-shift a6 i1)))
        (a23
         (swb32-havoc21-value
          a18
          (swb32-l-size)
          (swb32-shift a20 i1)))
        (a24
         (swb32-havoc21-value
          a18
          (swb32-l-size)
          a11))
        (a25 (swb32-shift a20 0)))
     (implies
      (and
       (not (equal x 2))
       (not (equal x2 0))
       (<= 0 i)
       (< i (swb32-l-size))
       (<= 0 i2)
       (<= i2 (swb32-l-size))
       (<= 0 x1)
       (< x1 (swb32-l-size))
       (<= (swb32-region (swb32-address-base a)) 0)
       (<= (swb32-region (swb32-address-base a1)) 0)
       (swb32-framed-p)
       (swb32-linked-p)
       (swb32-is-uint32-p i)
       (swb32-is-sint32-p i1)
       (swb32-is-sint32-p i2)
       (swb32-valid-rd-p a1 5)
       (swb32-is-uint32-p x)
       (swb32-is-sint32-p x1)
       (swb32-valid-rd-p a3 1)
       (swb32-valid-rd-p a7 1)
       (swb32-valid-rd-p a2 1)
       (swb32-valid-rd-p a8 1)
       (swb32-valid-rd-p a9 1)
       (swb32-valid-rd-p a4 1)
       (swb32-valid-rd-p
        (swb32-t4 (swb32-shift a1 2))
        2)
       (swb32-valid-rd-p a10 2)
       (swb32-is-sint32-p (swb32-t3 a11))
       (swb32-valid-rd-p a12 1)
       (swb32-valid-rd-p a5 1)
       (swb32-valid-rd-p a13 1)
       (swb32-valid-rd-p a14 1)
       (swb32-valid-rd-p a15 1)
       (swb32-is-uint8-p x2)
       (swb32-valid-rd-p a16 (swb32-l-size))
       (swb32-valid-rw-p a18 (swb32-l-size))
       (swb32-is-uint8-p
        (swb32-havoc19-value
         a18
         (swb32-l-size)
         (swb32-shift a6 -1)))
       (swb32-is-uint8-p
        (swb32-havoc19-value
         a18
         (swb32-l-size)
         (swb32-shift a20 -1)))
       (swb32-is-uint8-p a22)
       (swb32-is-uint8-p a23)
       (swb32-is-sint32-p
        (swb32-havoc19-value
         a18
         (swb32-l-size)
         a11))
       (swb32-is-sint32-p a24)
       (swb32-valid-rd-p a25 (swb32-l-size))
       (swb32-separated-p
        a18
        (swb32-l-size)
        a25
        (swb32-l-size))
       (implies
        (not
         (equal
          (swb32-land 7 a24)
          0))
        (equal i1 -1))
       (implies
        (not (equal i1 -1))
        (and
         (not (equal (swb32-l-idle-cpu i1) 0))
         (not (equal a22 0))
         (not (equal a23 0))
         (<= 0 i1)
         (< i1 (swb32-l-size))))
       (implies
        (equal i1 -1)
        (swb32-a20-to-a17-p a18 a20 a17))
       (implies
        (not (equal i1 -1))
        (swb32-selected-prefix-idle-zero-p
         a18 a6 a20 i1))
       (implies
        (equal i1 -1)
        (swb32-selected-prefix-idle-zero-p
         a18 a6 a20 i2))
       (implies
        (not (equal i1 -1))
        (swb32-selected-range-not-idle-core-p
         a18 a6 a20 i1 i2))
       (implies
        (not (equal i1 -1))
        (swb32-a20-to-a17-or-not-idle-core-p
         a18 a20 a17))
       (swb32-a16-separated-p a16 a)
       (swb32-array-layout-p a)
       (swb32-havoc19-agreement-p a18 a20 a17)
       (swb32-a17-to-a20-p a18 a17 a20)
       (swb32-sched-group-cpus-layout-p a)
       (swb32-sched-group-mask-layout-p a)
       (swb32-group-balance-mask-layout-p a)
       (swb32-cpu-smt-layout-p a))
      (swb32-valid-rd-p
       a18
       (swb32-l-size))))))

(defun-sk
    ntp4vc-should-we-balance-call-find-next-and-bit-pre-2-goal32-statement ()
  (forall
   (a1 a i i1 i2)
   (swb32-goal-body a1 a i i1 i2)))

(value-triple :itpeval-statement-checked)

:q
