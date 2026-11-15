;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_5_goal7:
;; readability of the scheduling-structure field at offset three under the
;; stated integer ranges, memory validity, framing, separation, and CPU-mask
;; layout hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb7-address-base (address)
  (car address))

(defun swb7-address-offset (address)
  (cdr address))

(defun swb7-shift (address amount)
  (cons
   (swb7-address-base address)
   (+ (swb7-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source integer memory t_1,
;; pointer memory t_2, allocation map t, and the fixed source symbols.

(defstub swb7-integer-memory (address) t)
(defstub swb7-pointer-memory (address) t)
(defstub swb7-allocation (index) t)
(defstub swb7-region (base) t)
(defstub swb7-linked-op () t)
(defstub swb7-l-size () t)
(defstub swb7-l-idle-cpu (index) t)
(defstub swb7-mask-memory-apply (memory-symbol address) t)
(defstub swb7-mask-pointer-apply (pointer-symbol address) t)
(defstub swb7-l-sched-group-cpus (address) t)
(defstub swb7-l-sched-group-mask (address) t)
(defstub swb7-l-group-balance-mask (address) t)
(defstub swb7-l-cpu-smt-mask (index) t)

(defun swb7-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb7-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb7-address-p address)
      (and
       (integerp
        (swb7-mask-memory-apply
         memory-symbol address))
       (swb7-address-p
        (swb7-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb7-is-uint8-p
        (swb7-l-idle-cpu index))
       (swb7-address-p
        (swb7-l-cpu-smt-mask index)))))))

(defun-sk swb7-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb7-address-p address)
     (equal
      (swb7-mask-memory-apply
       'swb7-zero-memory address)
      0))))

(defun-sk swb7-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb7-l-size)))
     (not
      (equal
       (swb7-mask-memory-apply
        memory-symbol
        (swb7-shift
         (swb7-mask-pointer-apply
          pointer-symbol
          (swb7-shift
           (swb7-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb7-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb7-mask-memory-apply
         memory-symbol
         (swb7-shift
          (swb7-mask-pointer-apply
           pointer-symbol
           (swb7-shift
            (swb7-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb7-l-size))
      (<= 0 j)
      (< j (swb7-l-size)))
     (not
      (equal
       (swb7-mask-memory-apply
        memory-symbol
        (swb7-shift
         (swb7-mask-pointer-apply
          pointer-symbol
          (swb7-shift
           (swb7-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb7-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb7-mask-memory-apply
         memory-symbol
         (swb7-shift
          (swb7-mask-pointer-apply
           pointer-symbol
           (swb7-shift
            (swb7-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb7-mask-memory-apply
         memory-symbol
         (swb7-shift
          (swb7-mask-pointer-apply
           pointer-symbol
           (swb7-shift
            (swb7-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb7-l-size))
      (<= 0 j)
      (< j (swb7-l-size))
      (<= 0 k)
      (< k (swb7-l-size)))
     (not
      (equal
       (swb7-mask-memory-apply
        memory-symbol
        (swb7-shift
         (swb7-mask-pointer-apply
          pointer-symbol
          (swb7-shift
           (swb7-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb7-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are exactly the source function types, expressed over the full
;; unbounded integer and address domains.

(defun-sk swb7-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb7-address-p address)
      (and
       (integerp (swb7-integer-memory address))
       (swb7-address-p (swb7-pointer-memory address))
       (swb7-address-p
        (swb7-l-sched-group-cpus address))
       (swb7-address-p
        (swb7-l-sched-group-mask address))
       (swb7-address-p
        (swb7-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb7-allocation index))
       (swb7-address-p (swb7-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb7-region base))))))

(defun swb7-linked-p ()
  (if (swb7-linked-op) t nil))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb7-address-base address))
    (<= 0 (swb7-address-offset address))
    (<=
     (+ (swb7-address-offset address) length)
     (swb7-allocation (swb7-address-base address))))))

(defun swb7-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb7-address-base address)))
    (<= 0 (swb7-address-offset address))
    (<=
     (+ (swb7-address-offset address) length)
     (swb7-allocation (swb7-address-base address))))))

(defun swb7-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb7-address-base left)
     (swb7-address-base right)))
   (<=
    (+ (swb7-address-offset right) right-length)
    (swb7-address-offset left))
   (<=
    (+ (swb7-address-offset left) left-length)
    (swb7-address-offset right))))

;; Exact unfolding of Memory.framed for t_2.

(defun-sk swb7-framed-p ()
  (forall (address)
    (implies
     (swb7-address-p address)
     (<=
      (swb7-region
       (swb7-address-base
        (swb7-pointer-memory address)))
      0))))

;; Separation from every pointed-to mask in the source array.

(defun-sk swb7-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb7-l-size))
       (swb7-separated-p
        mask
        (swb7-l-size)
        (swb7-shift
         (swb7-pointer-memory
          (swb7-shift
           (swb7-shift a index)
           0))
         0)
        (swb7-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb7-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((array-entry (swb7-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb7-l-size))
         (and
          (swb7-valid-rd-p array-entry 1)
          (swb7-valid-rw-p
           (swb7-shift
            (swb7-pointer-memory
             (swb7-shift array-entry 0))
            0)
           (swb7-l-size)))))))))

;; The three address-indexed scheduling layouts from the source hypotheses.

(defun-sk swb7-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb7-address-p address)
     (let*
         ((group-field
           (swb7-l-sched-group-cpus address))
          (group-mask
           (swb7-shift
            (swb7-pointer-memory
             (swb7-shift group-field 0))
            0)))
       (and
        (swb7-valid-rd-p group-field 1)
        (swb7-valid-rd-p group-mask (swb7-l-size))
        (swb7-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb7-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb7-address-p address)
     (let*
         ((group-field
           (swb7-l-sched-group-mask address))
          (group-mask
           (swb7-shift
            (swb7-pointer-memory
             (swb7-shift group-field 0))
            0)))
       (and
        (swb7-valid-rd-p group-field 1)
        (swb7-valid-rd-p group-mask (swb7-l-size))
        (swb7-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb7-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb7-address-p address)
     (let*
         ((group-field
           (swb7-l-group-balance-mask address))
          (group-mask
           (swb7-shift
            (swb7-pointer-memory
             (swb7-shift group-field 0))
            0)))
       (and
        (swb7-valid-rd-p group-field 1)
        (swb7-valid-rd-p group-mask (swb7-l-size))
        (swb7-separated-from-array-masks-p
         group-mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb7-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((cpu-field (swb7-l-cpu-smt-mask index))
          (cpu-mask
           (swb7-shift
            (swb7-pointer-memory
             (swb7-shift cpu-field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb7-l-size))
         (and
          (swb7-valid-rd-p cpu-field 1)
          (swb7-valid-rd-p cpu-mask (swb7-l-size))
          (swb7-separated-from-array-masks-p
           cpu-mask a))))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-5-goal7-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (swb7-function-types-p)
     (swb7-scheduler-schema-types-p)
     (swb7-zero-mask-memory-instance-p)
     (swb7-q-mask-refl-p)
     (swb7-q-mask-symm-p)
     (swb7-q-mask-trans-p)
     (integerp (swb7-l-size))
     (< 0 (swb7-l-size))
     (<= (swb7-l-size) 2147483647)
     (swb7-address-p a1)
     (integerp i)
     (swb7-address-p a))
    (let*
        ((a2 (swb7-shift a1 4))
         (a3 (swb7-pointer-memory a2))
         (a4
          (swb7-pointer-memory
           (swb7-shift a3 0)))
         (a5 (swb7-shift a1 1))
         (x (swb7-integer-memory a5))
         (x1
          (swb7-integer-memory
           (swb7-shift a4 x)))
         (a6 (swb7-shift a1 3))
         (a7 (swb7-shift a1 0))
         (a8 (swb7-pointer-memory a7))
         (a9 (swb7-shift a8 0))
         (a10 (swb7-shift a4 0)))
      (implies
       (and
        (not (equal x1 0))
        (<= 0 i)
        (< i (swb7-l-size))
        (<= 0 x)
        (< x (swb7-l-size))
        (<=
         (swb7-region (swb7-address-base a))
         0)
        (<=
         (swb7-region (swb7-address-base a1))
         0)
        (swb7-framed-p)
        (swb7-linked-p)
        (swb7-is-uint32-p i)
        (swb7-valid-rd-p a1 5)
        (swb7-is-uint32-p
         (swb7-integer-memory a6))
        (swb7-is-sint32-p x)
        (swb7-valid-rd-p a2 1)
        (swb7-valid-rd-p a5 1)
        (swb7-valid-rd-p a7 1)
        (swb7-valid-rd-p a3 1)
        (swb7-valid-rd-p
         (swb7-pointer-memory
          (swb7-shift a1 2))
         2)
        (swb7-valid-rd-p a8 2)
        (swb7-is-sint32-p
         (swb7-integer-memory
          (swb7-shift a8 1)))
        (swb7-valid-rd-p a9 1)
        (swb7-valid-rd-p
         (swb7-pointer-memory a9)
         1)
        (swb7-is-uint8-p x1)
        (swb7-valid-rd-p a10 (swb7-l-size))
        (swb7-separated-from-array-masks-p a10 a)
        (swb7-array-layout-p a)
        (swb7-sched-group-cpus-layout-p a)
        (swb7-sched-group-mask-layout-p a)
        (swb7-group-balance-mask-layout-p a)
        (swb7-cpu-smt-layout-p a))
       (swb7-valid-rd-p a6 1))))))

(value-triple :itpeval-statement-checked)

:q
