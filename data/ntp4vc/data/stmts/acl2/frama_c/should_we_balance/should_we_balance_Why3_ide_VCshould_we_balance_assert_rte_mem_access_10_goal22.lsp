;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_10_goal22:
;; readability of the selected scheduling-array entry under the stated integer
;; ranges, memory validity, framing, separation, havoc, CPU-mask layout, and
;; quantified scheduling hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb22-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb22-address-base (address)
  (car address))

(defun swb22-address-offset (address)
  (cdr address))

(defun swb22-shift (address amount)
  (cons
   (swb22-address-base address)
   (+ (swb22-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memory functions t_1,
;; t_2, t_3, t_4, allocation map t, and the fixed source symbols.

(defstub swb22-t1 (address) t)
(defstub swb22-t2 (address) t)
(defstub swb22-t3 (address) t)
(defstub swb22-t4 (address) t)
(defstub swb22-allocation (index) t)
(defstub swb22-region (base) t)
(defstub swb22-linked-op () t)
(defstub swb22-l-size () t)
(defstub swb22-mask-memory-apply (memory-symbol address) t)
(defstub swb22-mask-pointer-apply (pointer-symbol address) t)
(defstub swb22-l-idle-cpu (index) t)
(defstub swb22-l-sched-group-cpus (address) t)
(defstub swb22-l-sched-group-mask (address) t)
(defstub swb22-l-group-balance-mask (address) t)
(defstub swb22-l-cpu-smt-mask (index) t)

(defun swb22-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb22-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb22-address-p address)
      (and
       (integerp
        (swb22-mask-memory-apply
         memory-symbol address))
       (swb22-address-p
        (swb22-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb22-is-uint8-p
        (swb22-l-idle-cpu index))
       (swb22-address-p
        (swb22-l-cpu-smt-mask index)))))))

(defun-sk swb22-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb22-address-p address)
     (equal
      (swb22-mask-memory-apply
       'swb22-zero-memory address)
      0))))

(defun-sk swb22-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb22-l-size)))
     (not
      (equal
       (swb22-mask-memory-apply
        memory-symbol
        (swb22-shift
         (swb22-mask-pointer-apply
          pointer-symbol
          (swb22-shift
           (swb22-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb22-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb22-mask-memory-apply
         memory-symbol
         (swb22-shift
          (swb22-mask-pointer-apply
           pointer-symbol
           (swb22-shift
            (swb22-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb22-l-size))
      (<= 0 j)
      (< j (swb22-l-size)))
     (not
      (equal
       (swb22-mask-memory-apply
        memory-symbol
        (swb22-shift
         (swb22-mask-pointer-apply
          pointer-symbol
          (swb22-shift
           (swb22-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb22-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb22-mask-memory-apply
         memory-symbol
         (swb22-shift
          (swb22-mask-pointer-apply
           pointer-symbol
           (swb22-shift
            (swb22-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb22-mask-memory-apply
         memory-symbol
         (swb22-shift
          (swb22-mask-pointer-apply
           pointer-symbol
           (swb22-shift
            (swb22-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb22-l-size))
      (<= 0 j)
      (< j (swb22-l-size))
      (<= 0 k)
      (< k (swb22-l-size)))
     (not
      (equal
       (swb22-mask-memory-apply
        memory-symbol
        (swb22-shift
         (swb22-mask-pointer-apply
          pointer-symbol
          (swb22-shift
           (swb22-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb22-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb22-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun-sk swb22-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb22-address-p address)
      (and
       (integerp (swb22-t1 address))
       (integerp (swb22-t2 address))
       (integerp (swb22-t3 address))
       (swb22-address-p (swb22-t4 address))
       (swb22-address-p
        (swb22-l-sched-group-cpus address))
       (swb22-address-p
        (swb22-l-sched-group-mask address))
       (swb22-address-p
        (swb22-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb22-allocation index))
       (swb22-is-uint8-p (swb22-l-idle-cpu index))
       (swb22-address-p (swb22-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb22-region base))))))

(defun swb22-linked-p ()
  (if (swb22-linked-op) t nil))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swb22-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb22-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb22-address-base address))
    (<= 0 (swb22-address-offset address))
    (<=
     (+ (swb22-address-offset address) length)
     (swb22-allocation (swb22-address-base address))))))

(defun swb22-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb22-address-base address)))
    (<= 0 (swb22-address-offset address))
    (<=
     (+ (swb22-address-offset address) length)
     (swb22-allocation (swb22-address-base address))))))

(defun swb22-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb22-address-base left)
     (swb22-address-base right)))
   (<=
    (+ (swb22-address-offset right) right-length)
    (swb22-address-offset left))
   (<=
    (+ (swb22-address-offset left) left-length)
    (swb22-address-offset right))))

;; Exact unfolding of Memory.framed for t_4.

(defun-sk swb22-framed-p ()
  (forall (address)
    (implies
     (swb22-address-p address)
     (<=
      (swb22-region
       (swb22-address-base (swb22-t4 address)))
      0))))

;; Exact havoc_access values for the two source havoc expressions.

(defun swb22-havoc18-value
    (protected-start protected-length query)
  (if
      (swb22-separated-p
       query 1 protected-start protected-length)
      (swb22-t3 query)
    (swb22-t1 query)))

(defun swb22-havoc20-value
    (protected-start protected-length query)
  (if
      (swb22-separated-p
       query 1 protected-start protected-length)
      (swb22-t3 query)
    (swb22-t2 query)))

;; Exact unfolding of p_idle_core for t_4 and the havoced memory a_20.

(defun-sk swb22-idle-core-p (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb22-havoc20-value
         protected-start
         (swb22-l-size)
         (swb22-shift
          (swb22-t4
           (swb22-shift
            (swb22-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb22-l-size))
        (not
         (equal
          (swb22-l-idle-cpu index)
          0))))))))

;; When i_1 is -1, every selected a_19 position is selected in a_16.

(defun-sk swb22-a19-to-a16-p
    (protected-start a19 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb22-havoc20-value
         protected-start
         (swb22-l-size)
         (swb22-shift a19 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb22-l-size))
        (not
         (equal
          (swb22-havoc20-value
           protected-start
           (swb22-l-size)
           (swb22-shift a16 index))
          0))))))))

;; Every position selected by both masks below the given bound has an idle-CPU
;; value of zero.

(defun-sk swb22-selected-prefix-idle-zero-p
    (protected-start a5 a19 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb22-havoc20-value
         protected-start
         (swb22-l-size)
         (swb22-shift a5 index))
        0))
      (implies
       (not
        (equal
         (swb22-havoc20-value
          protected-start
          (swb22-l-size)
          (swb22-shift a19 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index bound)
         (implies
          (< index (swb22-l-size))
          (equal
           (swb22-l-idle-cpu index)
           0)))))))))

;; Every position selected by both masks in [i_1, i_2) is not an idle core.

(defun-sk swb22-selected-range-not-idle-core-p
    (protected-start a5 a19 i1 i2)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb22-havoc20-value
         protected-start
         (swb22-l-size)
         (swb22-shift a5 index))
        0))
      (implies
       (not
        (equal
         (swb22-havoc20-value
          protected-start
          (swb22-l-size)
          (swb22-shift a19 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= i1 index)
         (implies
          (< index i2)
          (implies
           (< index (swb22-l-size))
           (not
            (swb22-idle-core-p
             protected-start index)))))))))))

;; A selected a_19 position has either a selected a_16 position or is not an
;; idle core.

(defun-sk swb22-a19-to-a16-or-not-idle-core-p
    (protected-start a19 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb22-havoc20-value
         protected-start
         (swb22-l-size)
         (swb22-shift a19 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb22-l-size))
        (or
         (not
          (equal
           (swb22-havoc20-value
            protected-start
            (swb22-l-size)
            (swb22-shift a16 index))
           0))
         (not
          (swb22-idle-core-p
           protected-start index)))))))))

;; Separation of a_14 from every pointed-to array mask.

(defun-sk swb22-a14-separated-p (a14 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb22-l-size))
       (swb22-separated-p
        a14
        (swb22-l-size)
        (swb22-shift
         (swb22-t4
          (swb22-shift
           (swb22-shift a index)
           0))
         0)
        (swb22-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb22-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((a25 (swb22-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb22-l-size))
         (and
          (swb22-valid-rd-p a25 1)
          (swb22-valid-rw-p
           (swb22-shift
            (swb22-t4
             (swb22-shift a25 0))
            0)
           (swb22-l-size)))))))))

;; The two a_18 mask views agree at every valid index.

(defun-sk swb22-havoc18-agreement-p
    (protected-start a19 a16)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb22-l-size))
       (iff
        (not
         (equal
          (swb22-havoc18-value
           protected-start
           (swb22-l-size)
           (swb22-shift a19 index))
          0))
        (not
         (equal
          (swb22-havoc18-value
           protected-start
           (swb22-l-size)
           (swb22-shift a16 index))
          0))))))))

;; Every selected a_16 position is selected in a_19.

(defun-sk swb22-a16-to-a19-p
    (protected-start a16 a19)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb22-havoc20-value
         protected-start
         (swb22-l-size)
         (swb22-shift a16 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb22-l-size))
        (not
         (equal
          (swb22-havoc20-value
           protected-start
           (swb22-l-size)
           (swb22-shift a19 index))
          0))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb22-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb22-l-size))
       (swb22-separated-p
        mask
        (swb22-l-size)
        (swb22-shift
         (swb22-t4
          (swb22-shift
           (swb22-shift a index)
           0))
         0)
        (swb22-l-size)))))))

(defun-sk swb22-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb22-address-p address)
     (let*
         ((a26 (swb22-l-sched-group-cpus address))
          (a27
           (swb22-shift
            (swb22-t4
             (swb22-shift a26 0))
            0)))
       (and
        (swb22-valid-rd-p a26 1)
        (swb22-valid-rd-p a27 (swb22-l-size))
        (swb22-separated-from-array-masks-p a27 a))))))

(defun-sk swb22-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb22-address-p address)
     (let*
         ((a26 (swb22-l-sched-group-mask address))
          (a27
           (swb22-shift
            (swb22-t4
             (swb22-shift a26 0))
            0)))
       (and
        (swb22-valid-rd-p a26 1)
        (swb22-valid-rd-p a27 (swb22-l-size))
        (swb22-separated-from-array-masks-p a27 a))))))

(defun-sk swb22-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb22-address-p address)
     (let*
         ((a26 (swb22-l-group-balance-mask address))
          (a27
           (swb22-shift
            (swb22-t4
             (swb22-shift a26 0))
            0)))
       (and
        (swb22-valid-rd-p a26 1)
        (swb22-valid-rd-p a27 (swb22-l-size))
        (swb22-separated-from-array-masks-p a27 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb22-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((a25 (swb22-l-cpu-smt-mask index))
          (a26
           (swb22-shift
            (swb22-t4
             (swb22-shift a25 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb22-l-size))
         (and
          (swb22-valid-rd-p a25 1)
          (swb22-valid-rd-p a26 (swb22-l-size))
          (swb22-separated-from-array-masks-p a26 a))))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-10-goal22-statement ()
  (forall
   (a1 a i i1 i2)
   (implies
    (and
     (swb22-function-types-p)
     (swb22-scheduler-schema-types-p)
     (swb22-zero-mask-memory-instance-p)
     (swb22-q-mask-refl-p)
     (swb22-q-mask-symm-p)
     (swb22-q-mask-trans-p)
     (integerp (swb22-l-size))
     (< 0 (swb22-l-size))
     (<= (swb22-l-size) 2147483647)
     (swb22-address-p a1)
     (swb22-address-p a)
     (integerp i)
     (integerp i1)
     (integerp i2))
    (let*
        ((a2 (swb22-shift a1 3))
         (x (swb22-t3 a2))
         (a3 (swb22-shift a1 4))
         (a4 (swb22-t4 a3))
         (a5
          (swb22-t4
           (swb22-shift a4 0)))
         (a6 (swb22-shift a1 1))
         (x1 (swb22-t3 a6))
         (x2
          (swb22-t3
           (swb22-shift a5 x1)))
         (a7 (swb22-shift a1 0))
         (a8 (swb22-shift a i))
         (a9 (swb22-t4 a7))
         (a10 (swb22-shift a9 1))
         (a11 (swb22-shift a9 0))
         (a12 (swb22-t4 a11))
         (a13
          (swb22-l-group-balance-mask a12))
         (a14 (swb22-shift a5 0))
         (a15 (swb22-shift a8 0))
         (a16 (swb22-t4 a15))
         (a17 (swb22-shift a16 0))
         (a19
          (swb22-t4
           (swb22-shift a13 0)))
         (a21
          (swb22-havoc20-value
           a17
           (swb22-l-size)
           (swb22-shift a5 i1)))
         (a22
          (swb22-havoc20-value
           a17
           (swb22-l-size)
           (swb22-shift a19 i1)))
         (a23
          (swb22-havoc20-value
           a17
           (swb22-l-size)
           a10))
         (a24 (swb22-shift a19 0)))
      (implies
       (and
        (not (equal x 2))
        (not (equal x2 0))
        (<= 0 i)
        (< i (swb22-l-size))
        (<= 0 i2)
        (<= i2 (swb22-l-size))
        (<= 0 x1)
        (< x1 (swb22-l-size))
        (<= (swb22-region (swb22-address-base a)) 0)
        (<= (swb22-region (swb22-address-base a1)) 0)
        (swb22-framed-p)
        (swb22-linked-p)
        (swb22-is-uint32-p i)
        (swb22-is-sint32-p i1)
        (swb22-is-sint32-p i2)
        (swb22-valid-rd-p a1 5)
        (swb22-is-uint32-p x)
        (swb22-is-sint32-p x1)
        (swb22-valid-rd-p a3 1)
        (swb22-valid-rd-p a6 1)
        (swb22-valid-rd-p a2 1)
        (swb22-valid-rd-p a7 1)
        (swb22-valid-rd-p a8 1)
        (swb22-valid-rd-p a4 1)
        (swb22-valid-rd-p
         (swb22-t4 (swb22-shift a1 2))
         2)
        (swb22-valid-rd-p a9 2)
        (swb22-is-sint32-p (swb22-t3 a10))
        (swb22-valid-rd-p a11 1)
        (swb22-valid-rd-p a12 1)
        (swb22-valid-rd-p a13 1)
        (swb22-is-uint8-p x2)
        (swb22-valid-rd-p a14 (swb22-l-size))
        (swb22-valid-rw-p a17 (swb22-l-size))
        (swb22-is-uint8-p
         (swb22-havoc18-value
          a17
          (swb22-l-size)
          (swb22-shift a5 -1)))
        (swb22-is-uint8-p
         (swb22-havoc18-value
          a17
          (swb22-l-size)
          (swb22-shift a19 -1)))
        (swb22-is-uint8-p a21)
        (swb22-is-uint8-p a22)
        (swb22-is-sint32-p
         (swb22-havoc18-value
          a17
          (swb22-l-size)
          a10))
        (swb22-is-sint32-p a23)
        (swb22-valid-rd-p a24 (swb22-l-size))
        (swb22-separated-p
         a17
         (swb22-l-size)
         a24
         (swb22-l-size))
        (implies
         (not
          (equal
           (swb22-land 7 a23)
           0))
         (equal i1 -1))
        (implies
         (not (equal i1 -1))
         (and
          (not (equal (swb22-l-idle-cpu i1) 0))
          (not (equal a21 0))
          (not (equal a22 0))
          (<= 0 i1)
          (< i1 (swb22-l-size))))
        (implies
         (equal i1 -1)
         (swb22-a19-to-a16-p a17 a19 a16))
        (implies
         (not (equal i1 -1))
         (swb22-selected-prefix-idle-zero-p
          a17 a5 a19 i1))
        (implies
         (equal i1 -1)
         (swb22-selected-prefix-idle-zero-p
          a17 a5 a19 i2))
        (implies
         (not (equal i1 -1))
         (swb22-selected-range-not-idle-core-p
          a17 a5 a19 i1 i2))
        (implies
         (not (equal i1 -1))
         (swb22-a19-to-a16-or-not-idle-core-p
          a17 a19 a16))
        (swb22-a14-separated-p a14 a)
        (swb22-array-layout-p a)
        (swb22-havoc18-agreement-p a17 a19 a16)
        (swb22-a16-to-a19-p a17 a16 a19)
        (swb22-sched-group-cpus-layout-p a)
        (swb22-sched-group-mask-layout-p a)
        (swb22-group-balance-mask-layout-p a)
        (swb22-cpu-smt-layout-p a))
       (swb22-valid-rd-p a15 1))))))

(value-triple :itpeval-statement-checked)

:q
