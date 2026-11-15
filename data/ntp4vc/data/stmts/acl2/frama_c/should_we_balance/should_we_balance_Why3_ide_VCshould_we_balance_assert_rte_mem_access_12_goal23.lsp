;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_12_goal23:
;; readability of the intermediate scheduling pointer under the stated integer
;; ranges, memory validity, framing, separation, havoc, CPU-mask layout, and
;; quantified scheduling hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb23-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb23-address-base (address)
  (car address))

(defun swb23-address-offset (address)
  (cdr address))

(defun swb23-shift (address amount)
  (cons
   (swb23-address-base address)
   (+ (swb23-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memory functions t_1,
;; t_2, t_3, t_4, allocation map t, and the fixed source symbols.

(defstub swb23-t1 (address) t)
(defstub swb23-t2 (address) t)
(defstub swb23-t3 (address) t)
(defstub swb23-t4 (address) t)
(defstub swb23-allocation (index) t)
(defstub swb23-region (base) t)
(defstub swb23-linked-op () t)
(defstub swb23-l-size () t)
(defstub swb23-mask-memory-apply (memory-symbol address) t)
(defstub swb23-mask-pointer-apply (pointer-symbol address) t)
(defstub swb23-l-idle-cpu (index) t)
(defstub swb23-l-sched-group-cpus (address) t)
(defstub swb23-l-sched-group-mask (address) t)
(defstub swb23-l-group-balance-mask (address) t)
(defstub swb23-l-cpu-smt-mask (index) t)

(defun swb23-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb23-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb23-address-p address)
      (and
       (integerp
        (swb23-mask-memory-apply
         memory-symbol address))
       (swb23-address-p
        (swb23-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb23-is-uint8-p
        (swb23-l-idle-cpu index))
       (swb23-address-p
        (swb23-l-cpu-smt-mask index)))))))

(defun-sk swb23-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb23-address-p address)
     (equal
      (swb23-mask-memory-apply
       'swb23-zero-memory address)
      0))))

(defun-sk swb23-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb23-l-size)))
     (not
      (equal
       (swb23-mask-memory-apply
        memory-symbol
        (swb23-shift
         (swb23-mask-pointer-apply
          pointer-symbol
          (swb23-shift
           (swb23-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb23-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb23-mask-memory-apply
         memory-symbol
         (swb23-shift
          (swb23-mask-pointer-apply
           pointer-symbol
           (swb23-shift
            (swb23-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb23-l-size))
      (<= 0 j)
      (< j (swb23-l-size)))
     (not
      (equal
       (swb23-mask-memory-apply
        memory-symbol
        (swb23-shift
         (swb23-mask-pointer-apply
          pointer-symbol
          (swb23-shift
           (swb23-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb23-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb23-mask-memory-apply
         memory-symbol
         (swb23-shift
          (swb23-mask-pointer-apply
           pointer-symbol
           (swb23-shift
            (swb23-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb23-mask-memory-apply
         memory-symbol
         (swb23-shift
          (swb23-mask-pointer-apply
           pointer-symbol
           (swb23-shift
            (swb23-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb23-l-size))
      (<= 0 j)
      (< j (swb23-l-size))
      (<= 0 k)
      (< k (swb23-l-size)))
     (not
      (equal
       (swb23-mask-memory-apply
        memory-symbol
        (swb23-shift
         (swb23-mask-pointer-apply
          pointer-symbol
          (swb23-shift
           (swb23-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb23-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb23-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun-sk swb23-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb23-address-p address)
      (and
       (integerp (swb23-t1 address))
       (integerp (swb23-t2 address))
       (integerp (swb23-t3 address))
       (swb23-address-p (swb23-t4 address))
       (swb23-address-p
        (swb23-l-sched-group-cpus address))
       (swb23-address-p
        (swb23-l-sched-group-mask address))
       (swb23-address-p
        (swb23-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb23-allocation index))
       (swb23-is-uint8-p (swb23-l-idle-cpu index))
       (swb23-address-p (swb23-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb23-region base))))))

(defun swb23-linked-p ()
  (if (swb23-linked-op) t nil))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swb23-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb23-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb23-address-base address))
    (<= 0 (swb23-address-offset address))
    (<=
     (+ (swb23-address-offset address) length)
     (swb23-allocation (swb23-address-base address))))))

(defun swb23-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb23-address-base address)))
    (<= 0 (swb23-address-offset address))
    (<=
     (+ (swb23-address-offset address) length)
     (swb23-allocation (swb23-address-base address))))))

(defun swb23-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb23-address-base left)
     (swb23-address-base right)))
   (<=
    (+ (swb23-address-offset right) right-length)
    (swb23-address-offset left))
   (<=
    (+ (swb23-address-offset left) left-length)
    (swb23-address-offset right))))

;; Exact unfolding of Memory.framed for t_4.

(defun-sk swb23-framed-p ()
  (forall (address)
    (implies
     (swb23-address-p address)
     (<=
      (swb23-region
       (swb23-address-base (swb23-t4 address)))
      0))))

;; Exact havoc_access values for the two source havoc expressions.

(defun swb23-havoc18-value
    (protected-start protected-length query)
  (if
      (swb23-separated-p
       query 1 protected-start protected-length)
      (swb23-t3 query)
    (swb23-t1 query)))

(defun swb23-havoc20-value
    (protected-start protected-length query)
  (if
      (swb23-separated-p
       query 1 protected-start protected-length)
      (swb23-t3 query)
    (swb23-t2 query)))

;; Exact unfolding of p_idle_core for t_4 and the havoced memory a_20.

(defun-sk swb23-idle-core-p (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb23-havoc20-value
         protected-start
         (swb23-l-size)
         (swb23-shift
          (swb23-t4
           (swb23-shift
            (swb23-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb23-l-size))
        (not
         (equal
          (swb23-l-idle-cpu index)
          0))))))))

;; When i_1 is -1, every selected a_19 position is selected in a_16.

(defun-sk swb23-a19-to-a16-p
    (protected-start a19 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb23-havoc20-value
         protected-start
         (swb23-l-size)
         (swb23-shift a19 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb23-l-size))
        (not
         (equal
          (swb23-havoc20-value
           protected-start
           (swb23-l-size)
           (swb23-shift a16 index))
          0))))))))

;; Every position selected by both masks below the given bound has an idle-CPU
;; value of zero.

(defun-sk swb23-selected-prefix-idle-zero-p
    (protected-start a6 a19 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb23-havoc20-value
         protected-start
         (swb23-l-size)
         (swb23-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb23-havoc20-value
          protected-start
          (swb23-l-size)
          (swb23-shift a19 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index bound)
         (implies
          (< index (swb23-l-size))
          (equal
           (swb23-l-idle-cpu index)
           0)))))))))

;; Every position selected by both masks in [i_1, i_2) is not an idle core.

(defun-sk swb23-selected-range-not-idle-core-p
    (protected-start a6 a19 i1 i2)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb23-havoc20-value
         protected-start
         (swb23-l-size)
         (swb23-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb23-havoc20-value
          protected-start
          (swb23-l-size)
          (swb23-shift a19 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= i1 index)
         (implies
          (< index i2)
          (implies
           (< index (swb23-l-size))
           (not
            (swb23-idle-core-p
             protected-start index)))))))))))

;; A selected a_19 position has either a selected a_16 position or is not an
;; idle core.

(defun-sk swb23-a19-to-a16-or-not-idle-core-p
    (protected-start a19 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb23-havoc20-value
         protected-start
         (swb23-l-size)
         (swb23-shift a19 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb23-l-size))
        (or
         (not
          (equal
           (swb23-havoc20-value
            protected-start
            (swb23-l-size)
            (swb23-shift a16 index))
           0))
         (not
          (swb23-idle-core-p
           protected-start index)))))))))

;; Separation of a_15 from every pointed-to array mask.

(defun-sk swb23-a15-separated-p (a15 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb23-l-size))
       (swb23-separated-p
        a15
        (swb23-l-size)
        (swb23-shift
         (swb23-t4
          (swb23-shift
           (swb23-shift a index)
           0))
         0)
        (swb23-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb23-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((a25 (swb23-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb23-l-size))
         (and
          (swb23-valid-rd-p a25 1)
          (swb23-valid-rw-p
           (swb23-shift
            (swb23-t4
             (swb23-shift a25 0))
            0)
           (swb23-l-size)))))))))

;; The two a_18 mask views agree at every valid index.

(defun-sk swb23-havoc18-agreement-p
    (protected-start a19 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb23-l-size))
       (iff
        (not
         (equal
          (swb23-havoc18-value
           protected-start
           (swb23-l-size)
           (swb23-shift a19 index))
          0))
        (not
         (equal
          (swb23-havoc18-value
           protected-start
           (swb23-l-size)
           (swb23-shift a16 index))
          0))))))))

;; Every selected a_16 position is selected in a_19.

(defun-sk swb23-a16-to-a19-p
    (protected-start a16 a19)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb23-havoc20-value
         protected-start
         (swb23-l-size)
         (swb23-shift a16 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb23-l-size))
        (not
         (equal
          (swb23-havoc20-value
           protected-start
           (swb23-l-size)
           (swb23-shift a19 index))
          0))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb23-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb23-l-size))
       (swb23-separated-p
        mask
        (swb23-l-size)
        (swb23-shift
         (swb23-t4
          (swb23-shift
           (swb23-shift a index)
           0))
         0)
        (swb23-l-size)))))))

(defun-sk swb23-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb23-address-p address)
     (let*
         ((a26 (swb23-l-sched-group-cpus address))
          (a27
           (swb23-shift
            (swb23-t4
             (swb23-shift a26 0))
            0)))
       (and
        (swb23-valid-rd-p a26 1)
        (swb23-valid-rd-p a27 (swb23-l-size))
        (swb23-separated-from-array-masks-p a27 a))))))

(defun-sk swb23-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb23-address-p address)
     (let*
         ((a26 (swb23-l-sched-group-mask address))
          (a27
           (swb23-shift
            (swb23-t4
             (swb23-shift a26 0))
            0)))
       (and
        (swb23-valid-rd-p a26 1)
        (swb23-valid-rd-p a27 (swb23-l-size))
        (swb23-separated-from-array-masks-p a27 a))))))

(defun-sk swb23-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb23-address-p address)
     (let*
         ((a26 (swb23-l-group-balance-mask address))
          (a27
           (swb23-shift
            (swb23-t4
             (swb23-shift a26 0))
            0)))
       (and
        (swb23-valid-rd-p a26 1)
        (swb23-valid-rd-p a27 (swb23-l-size))
        (swb23-separated-from-array-masks-p a27 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb23-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((a25 (swb23-l-cpu-smt-mask index))
          (a26
           (swb23-shift
            (swb23-t4
             (swb23-shift a25 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb23-l-size))
         (and
          (swb23-valid-rd-p a25 1)
          (swb23-valid-rd-p a26 (swb23-l-size))
          (swb23-separated-from-array-masks-p a26 a))))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-12-goal23-statement ()
  (forall
   (a1 a i i1 i2)
   (implies
    (and
     (swb23-function-types-p)
     (swb23-scheduler-schema-types-p)
     (swb23-zero-mask-memory-instance-p)
     (swb23-q-mask-refl-p)
     (swb23-q-mask-symm-p)
     (swb23-q-mask-trans-p)
     (integerp (swb23-l-size))
     (< 0 (swb23-l-size))
     (<= (swb23-l-size) 2147483647)
     (swb23-address-p a1)
     (swb23-address-p a)
     (integerp i)
     (integerp i1)
     (integerp i2))
    (let*
        ((a2 (swb23-shift a1 3))
         (x (swb23-t3 a2))
         (a3 (swb23-shift a1 4))
         (a4 (swb23-t4 a3))
         (a5 (swb23-shift a4 0))
         (a6 (swb23-t4 a5))
         (a7 (swb23-shift a1 1))
         (x1 (swb23-t3 a7))
         (x2
          (swb23-t3
           (swb23-shift a6 x1)))
         (a8 (swb23-shift a1 0))
         (a9 (swb23-shift a i))
         (a10 (swb23-t4 a8))
         (a11 (swb23-shift a10 1))
         (a12 (swb23-shift a10 0))
         (a13 (swb23-t4 a12))
         (a14
          (swb23-l-group-balance-mask a13))
         (a15 (swb23-shift a6 0))
         (a16
          (swb23-t4
           (swb23-shift a9 0)))
         (a17 (swb23-shift a16 0))
         (a19
          (swb23-t4
           (swb23-shift a14 0)))
         (a21
          (swb23-havoc20-value
           a17
           (swb23-l-size)
           (swb23-shift a6 i1)))
         (a22
          (swb23-havoc20-value
           a17
           (swb23-l-size)
           (swb23-shift a19 i1)))
         (a23
          (swb23-havoc20-value
           a17
           (swb23-l-size)
           a11))
         (a24 (swb23-shift a19 0)))
      (implies
       (and
        (not (equal x 2))
        (not (equal x2 0))
        (<= 0 i)
        (< i (swb23-l-size))
        (<= 0 i2)
        (<= i2 (swb23-l-size))
        (<= 0 x1)
        (< x1 (swb23-l-size))
        (<= (swb23-region (swb23-address-base a)) 0)
        (<= (swb23-region (swb23-address-base a1)) 0)
        (swb23-framed-p)
        (swb23-linked-p)
        (swb23-is-uint32-p i)
        (swb23-is-sint32-p i1)
        (swb23-is-sint32-p i2)
        (swb23-valid-rd-p a1 5)
        (swb23-is-uint32-p x)
        (swb23-is-sint32-p x1)
        (swb23-valid-rd-p a3 1)
        (swb23-valid-rd-p a7 1)
        (swb23-valid-rd-p a2 1)
        (swb23-valid-rd-p a8 1)
        (swb23-valid-rd-p a9 1)
        (swb23-valid-rd-p a4 1)
        (swb23-valid-rd-p
         (swb23-t4 (swb23-shift a1 2))
         2)
        (swb23-valid-rd-p a10 2)
        (swb23-is-sint32-p (swb23-t3 a11))
        (swb23-valid-rd-p a12 1)
        (swb23-valid-rd-p a13 1)
        (swb23-valid-rd-p a14 1)
        (swb23-is-uint8-p x2)
        (swb23-valid-rd-p a15 (swb23-l-size))
        (swb23-valid-rw-p a17 (swb23-l-size))
        (swb23-is-uint8-p
         (swb23-havoc18-value
          a17
          (swb23-l-size)
          (swb23-shift a6 -1)))
        (swb23-is-uint8-p
         (swb23-havoc18-value
          a17
          (swb23-l-size)
          (swb23-shift a19 -1)))
        (swb23-is-uint8-p a21)
        (swb23-is-uint8-p a22)
        (swb23-is-sint32-p
         (swb23-havoc18-value
          a17
          (swb23-l-size)
          a11))
        (swb23-is-sint32-p a23)
        (swb23-valid-rd-p a24 (swb23-l-size))
        (swb23-separated-p
         a17
         (swb23-l-size)
         a24
         (swb23-l-size))
        (implies
         (not
          (equal
           (swb23-land 7 a23)
           0))
         (equal i1 -1))
        (implies
         (not (equal i1 -1))
         (and
          (not (equal (swb23-l-idle-cpu i1) 0))
          (not (equal a21 0))
          (not (equal a22 0))
          (<= 0 i1)
          (< i1 (swb23-l-size))))
        (implies
         (equal i1 -1)
         (swb23-a19-to-a16-p a17 a19 a16))
        (implies
         (not (equal i1 -1))
         (swb23-selected-prefix-idle-zero-p
          a17 a6 a19 i1))
        (implies
         (equal i1 -1)
         (swb23-selected-prefix-idle-zero-p
          a17 a6 a19 i2))
        (implies
         (not (equal i1 -1))
         (swb23-selected-range-not-idle-core-p
          a17 a6 a19 i1 i2))
        (implies
         (not (equal i1 -1))
         (swb23-a19-to-a16-or-not-idle-core-p
          a17 a19 a16))
        (swb23-a15-separated-p a15 a)
        (swb23-array-layout-p a)
        (swb23-havoc18-agreement-p a17 a19 a16)
        (swb23-a16-to-a19-p a17 a16 a19)
        (swb23-sched-group-cpus-layout-p a)
        (swb23-sched-group-mask-layout-p a)
        (swb23-group-balance-mask-layout-p a)
        (swb23-cpu-smt-layout-p a))
       (swb23-valid-rd-p a5 1))))))

(value-triple :itpeval-statement-checked)

:q
