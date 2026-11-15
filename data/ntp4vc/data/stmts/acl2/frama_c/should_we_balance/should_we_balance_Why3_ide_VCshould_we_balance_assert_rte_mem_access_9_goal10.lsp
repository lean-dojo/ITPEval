;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_9_goal10:
;; readability of the scheduling address one unit after the pointer selected
;; from the field at offset two, under the stated integer ranges, memory
;; validity, framing, separation, and CPU-mask layout hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb10-address-base (address)
  (car address))

(defun swb10-address-offset (address)
  (cdr address))

(defun swb10-shift (address amount)
  (cons
   (swb10-address-base address)
   (+ (swb10-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source integer memory t_1,
;; pointer memory t_2, allocation map t, and the fixed source symbols.

(defstub swb10-integer-memory (address) t)
(defstub swb10-pointer-memory (address) t)
(defstub swb10-allocation (index) t)
(defstub swb10-region (base) t)
(defstub swb10-linked-op () t)
(defstub swb10-l-size () t)
(defstub swb10-l-idle-cpu (index) t)
(defstub swb10-mask-memory-apply (memory-symbol address) t)
(defstub swb10-mask-pointer-apply (pointer-symbol address) t)
(defstub swb10-l-sched-group-cpus (address) t)
(defstub swb10-l-sched-group-mask (address) t)
(defstub swb10-l-group-balance-mask (address) t)
(defstub swb10-l-cpu-smt-mask (index) t)

(defun swb10-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb10-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb10-address-p address)
      (and
       (integerp
        (swb10-mask-memory-apply
         memory-symbol address))
       (swb10-address-p
        (swb10-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb10-is-uint8-p
        (swb10-l-idle-cpu index))
       (swb10-address-p
        (swb10-l-cpu-smt-mask index)))))))

(defun-sk swb10-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb10-address-p address)
     (equal
      (swb10-mask-memory-apply
       'swb10-zero-memory address)
      0))))

(defun-sk swb10-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb10-l-size)))
     (not
      (equal
       (swb10-mask-memory-apply
        memory-symbol
        (swb10-shift
         (swb10-mask-pointer-apply
          pointer-symbol
          (swb10-shift
           (swb10-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb10-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb10-mask-memory-apply
         memory-symbol
         (swb10-shift
          (swb10-mask-pointer-apply
           pointer-symbol
           (swb10-shift
            (swb10-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb10-l-size))
      (<= 0 j)
      (< j (swb10-l-size)))
     (not
      (equal
       (swb10-mask-memory-apply
        memory-symbol
        (swb10-shift
         (swb10-mask-pointer-apply
          pointer-symbol
          (swb10-shift
           (swb10-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb10-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb10-mask-memory-apply
         memory-symbol
         (swb10-shift
          (swb10-mask-pointer-apply
           pointer-symbol
           (swb10-shift
            (swb10-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb10-mask-memory-apply
         memory-symbol
         (swb10-shift
          (swb10-mask-pointer-apply
           pointer-symbol
           (swb10-shift
            (swb10-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb10-l-size))
      (<= 0 j)
      (< j (swb10-l-size))
      (<= 0 k)
      (< k (swb10-l-size)))
     (not
      (equal
       (swb10-mask-memory-apply
        memory-symbol
        (swb10-shift
         (swb10-mask-pointer-apply
          pointer-symbol
          (swb10-shift
           (swb10-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb10-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are exactly the source function types, expressed over the full
;; unbounded integer and address domains.

(defun-sk swb10-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb10-address-p address)
      (and
       (integerp (swb10-integer-memory address))
       (swb10-address-p (swb10-pointer-memory address))
       (swb10-address-p
        (swb10-l-sched-group-cpus address))
       (swb10-address-p
        (swb10-l-sched-group-mask address))
       (swb10-address-p
        (swb10-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb10-allocation index))
       (swb10-address-p (swb10-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb10-region base))))))

(defun swb10-linked-p ()
  (if (swb10-linked-op) t nil))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb10-address-base address))
    (<= 0 (swb10-address-offset address))
    (<=
     (+ (swb10-address-offset address) length)
     (swb10-allocation (swb10-address-base address))))))

(defun swb10-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb10-address-base address)))
    (<= 0 (swb10-address-offset address))
    (<=
     (+ (swb10-address-offset address) length)
     (swb10-allocation (swb10-address-base address))))))

(defun swb10-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb10-address-base left)
     (swb10-address-base right)))
   (<=
    (+ (swb10-address-offset right) right-length)
    (swb10-address-offset left))
   (<=
    (+ (swb10-address-offset left) left-length)
    (swb10-address-offset right))))

;; Exact unfolding of Memory.framed for t_2.

(defun-sk swb10-framed-p ()
  (forall (address)
    (implies
     (swb10-address-p address)
     (<=
      (swb10-region
       (swb10-address-base
        (swb10-pointer-memory address)))
      0))))

;; Separation from every pointed-to mask in the source array.

(defun-sk swb10-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb10-l-size))
       (swb10-separated-p
        mask
        (swb10-l-size)
        (swb10-shift
         (swb10-pointer-memory
          (swb10-shift
           (swb10-shift a index)
           0))
         0)
        (swb10-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb10-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((array-entry (swb10-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb10-l-size))
         (and
          (swb10-valid-rd-p array-entry 1)
          (swb10-valid-rw-p
           (swb10-shift
            (swb10-pointer-memory
             (swb10-shift array-entry 0))
            0)
           (swb10-l-size)))))))))

;; The three address-indexed scheduling layouts from the source hypotheses.

(defun-sk swb10-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb10-address-p address)
     (let*
         ((group-field
           (swb10-l-sched-group-cpus address))
          (group-mask
           (swb10-shift
            (swb10-pointer-memory
             (swb10-shift group-field 0))
            0)))
       (and
        (swb10-valid-rd-p group-field 1)
        (swb10-valid-rd-p group-mask (swb10-l-size))
        (swb10-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb10-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb10-address-p address)
     (let*
         ((group-field
           (swb10-l-sched-group-mask address))
          (group-mask
           (swb10-shift
            (swb10-pointer-memory
             (swb10-shift group-field 0))
            0)))
       (and
        (swb10-valid-rd-p group-field 1)
        (swb10-valid-rd-p group-mask (swb10-l-size))
        (swb10-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb10-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb10-address-p address)
     (let*
         ((group-field
           (swb10-l-group-balance-mask address))
          (group-mask
           (swb10-shift
            (swb10-pointer-memory
             (swb10-shift group-field 0))
            0)))
       (and
        (swb10-valid-rd-p group-field 1)
        (swb10-valid-rd-p group-mask (swb10-l-size))
        (swb10-separated-from-array-masks-p
         group-mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb10-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((cpu-field (swb10-l-cpu-smt-mask index))
          (cpu-mask
           (swb10-shift
            (swb10-pointer-memory
             (swb10-shift cpu-field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb10-l-size))
         (and
          (swb10-valid-rd-p cpu-field 1)
          (swb10-valid-rd-p cpu-mask (swb10-l-size))
          (swb10-separated-from-array-masks-p
           cpu-mask a))))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-9-goal10-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (swb10-function-types-p)
     (swb10-scheduler-schema-types-p)
     (swb10-zero-mask-memory-instance-p)
     (swb10-q-mask-refl-p)
     (swb10-q-mask-symm-p)
     (swb10-q-mask-trans-p)
     (integerp (swb10-l-size))
     (< 0 (swb10-l-size))
     (<= (swb10-l-size) 2147483647)
     (swb10-address-p a1)
     (integerp i)
     (swb10-address-p a))
    (let*
        ((a2 (swb10-shift a1 3))
         (a3 (swb10-shift a1 4))
         (a4 (swb10-pointer-memory a3))
         (a5
          (swb10-pointer-memory
           (swb10-shift a4 0)))
         (a6 (swb10-shift a1 1))
         (x (swb10-integer-memory a6))
         (x1
          (swb10-integer-memory
           (swb10-shift a5 x)))
         (a7 (swb10-shift a1 2))
         (a8 (swb10-pointer-memory a7))
         (a9 (swb10-shift a8 0))
         (x2 (swb10-integer-memory a9))
         (a10 (swb10-shift a1 0))
         (a11 (swb10-pointer-memory a10))
         (a12 (swb10-shift a8 1))
         (a13 (swb10-shift a11 0))
         (a14 (swb10-shift a5 0)))
      (implies
       (and
        (equal (swb10-integer-memory a2) 2)
        (not (equal x1 0))
        (<= 0 i)
        (< i (swb10-l-size))
        (<= 0 x)
        (< x (swb10-l-size))
        (<=
         (swb10-region (swb10-address-base a))
         0)
        (<=
         (swb10-region (swb10-address-base a1))
         0)
        (<= x2 0)
        (swb10-framed-p)
        (swb10-linked-p)
        (swb10-is-uint32-p i)
        (swb10-valid-rd-p a1 5)
        (swb10-is-sint32-p x)
        (swb10-valid-rd-p a3 1)
        (swb10-valid-rd-p a6 1)
        (swb10-valid-rd-p a7 1)
        (swb10-valid-rd-p a2 1)
        (swb10-valid-rd-p a10 1)
        (swb10-valid-rd-p a4 1)
        (swb10-valid-rd-p a8 2)
        (swb10-valid-rd-p a11 2)
        (swb10-is-uint32-p x2)
        (swb10-is-uint32-p
         (swb10-integer-memory a12))
        (swb10-is-sint32-p
         (swb10-integer-memory
          (swb10-shift a11 1)))
        (swb10-valid-rd-p a13 1)
        (swb10-valid-rd-p a9 1)
        (swb10-valid-rd-p
         (swb10-pointer-memory a13)
         1)
        (swb10-is-uint8-p x1)
        (swb10-valid-rd-p a14 (swb10-l-size))
        (swb10-separated-from-array-masks-p a14 a)
        (swb10-array-layout-p a)
        (swb10-sched-group-cpus-layout-p a)
        (swb10-sched-group-mask-layout-p a)
        (swb10-group-balance-mask-layout-p a)
        (swb10-cpu-smt-layout-p a))
       (swb10-valid-rd-p a12 1))))))

(value-triple :itpeval-statement-checked)

:q
