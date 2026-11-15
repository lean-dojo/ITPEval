;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_7_goal9:
;; readability of the scheduling pointer selected from the field at offset two
;; under the stated integer ranges, memory validity, framing, separation, and
;; CPU-mask layout hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb9-address-base (address)
  (car address))

(defun swb9-address-offset (address)
  (cdr address))

(defun swb9-shift (address amount)
  (cons
   (swb9-address-base address)
   (+ (swb9-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source integer memory t_1,
;; pointer memory t_2, allocation map t, and the fixed source symbols.

(defstub swb9-integer-memory (address) t)
(defstub swb9-pointer-memory (address) t)
(defstub swb9-allocation (index) t)
(defstub swb9-region (base) t)
(defstub swb9-linked-op () t)
(defstub swb9-l-size () t)
(defstub swb9-l-idle-cpu (index) t)
(defstub swb9-mask-memory-apply (memory-symbol address) t)
(defstub swb9-mask-pointer-apply (pointer-symbol address) t)
(defstub swb9-l-sched-group-cpus (address) t)
(defstub swb9-l-sched-group-mask (address) t)
(defstub swb9-l-group-balance-mask (address) t)
(defstub swb9-l-cpu-smt-mask (index) t)

(defun swb9-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb9-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb9-address-p address)
      (and
       (integerp
        (swb9-mask-memory-apply
         memory-symbol address))
       (swb9-address-p
        (swb9-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb9-is-uint8-p
        (swb9-l-idle-cpu index))
       (swb9-address-p
        (swb9-l-cpu-smt-mask index)))))))

(defun-sk swb9-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb9-address-p address)
     (equal
      (swb9-mask-memory-apply
       'swb9-zero-memory address)
      0))))

(defun-sk swb9-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb9-l-size)))
     (not
      (equal
       (swb9-mask-memory-apply
        memory-symbol
        (swb9-shift
         (swb9-mask-pointer-apply
          pointer-symbol
          (swb9-shift
           (swb9-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb9-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb9-mask-memory-apply
         memory-symbol
         (swb9-shift
          (swb9-mask-pointer-apply
           pointer-symbol
           (swb9-shift
            (swb9-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb9-l-size))
      (<= 0 j)
      (< j (swb9-l-size)))
     (not
      (equal
       (swb9-mask-memory-apply
        memory-symbol
        (swb9-shift
         (swb9-mask-pointer-apply
          pointer-symbol
          (swb9-shift
           (swb9-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb9-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb9-mask-memory-apply
         memory-symbol
         (swb9-shift
          (swb9-mask-pointer-apply
           pointer-symbol
           (swb9-shift
            (swb9-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb9-mask-memory-apply
         memory-symbol
         (swb9-shift
          (swb9-mask-pointer-apply
           pointer-symbol
           (swb9-shift
            (swb9-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb9-l-size))
      (<= 0 j)
      (< j (swb9-l-size))
      (<= 0 k)
      (< k (swb9-l-size)))
     (not
      (equal
       (swb9-mask-memory-apply
        memory-symbol
        (swb9-shift
         (swb9-mask-pointer-apply
          pointer-symbol
          (swb9-shift
           (swb9-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb9-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb9-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are exactly the source function types, expressed over the full
;; unbounded integer and address domains.

(defun-sk swb9-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb9-address-p address)
      (and
       (integerp (swb9-integer-memory address))
       (swb9-address-p (swb9-pointer-memory address))
       (swb9-address-p
        (swb9-l-sched-group-cpus address))
       (swb9-address-p
        (swb9-l-sched-group-mask address))
       (swb9-address-p
        (swb9-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb9-allocation index))
       (swb9-address-p (swb9-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb9-region base))))))

(defun swb9-linked-p ()
  (if (swb9-linked-op) t nil))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb9-address-base address))
    (<= 0 (swb9-address-offset address))
    (<=
     (+ (swb9-address-offset address) length)
     (swb9-allocation (swb9-address-base address))))))

(defun swb9-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb9-address-base address)))
    (<= 0 (swb9-address-offset address))
    (<=
     (+ (swb9-address-offset address) length)
     (swb9-allocation (swb9-address-base address))))))

(defun swb9-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb9-address-base left)
     (swb9-address-base right)))
   (<=
    (+ (swb9-address-offset right) right-length)
    (swb9-address-offset left))
   (<=
    (+ (swb9-address-offset left) left-length)
    (swb9-address-offset right))))

;; Exact unfolding of Memory.framed for t_2.

(defun-sk swb9-framed-p ()
  (forall (address)
    (implies
     (swb9-address-p address)
     (<=
      (swb9-region
       (swb9-address-base
        (swb9-pointer-memory address)))
      0))))

;; Separation from every pointed-to mask in the source array.

(defun-sk swb9-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb9-l-size))
       (swb9-separated-p
        mask
        (swb9-l-size)
        (swb9-shift
         (swb9-pointer-memory
          (swb9-shift
           (swb9-shift a index)
           0))
         0)
        (swb9-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb9-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((array-entry (swb9-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb9-l-size))
         (and
          (swb9-valid-rd-p array-entry 1)
          (swb9-valid-rw-p
           (swb9-shift
            (swb9-pointer-memory
             (swb9-shift array-entry 0))
            0)
           (swb9-l-size)))))))))

;; The three address-indexed scheduling layouts from the source hypotheses.

(defun-sk swb9-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb9-address-p address)
     (let*
         ((group-field
           (swb9-l-sched-group-cpus address))
          (group-mask
           (swb9-shift
            (swb9-pointer-memory
             (swb9-shift group-field 0))
            0)))
       (and
        (swb9-valid-rd-p group-field 1)
        (swb9-valid-rd-p group-mask (swb9-l-size))
        (swb9-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb9-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb9-address-p address)
     (let*
         ((group-field
           (swb9-l-sched-group-mask address))
          (group-mask
           (swb9-shift
            (swb9-pointer-memory
             (swb9-shift group-field 0))
            0)))
       (and
        (swb9-valid-rd-p group-field 1)
        (swb9-valid-rd-p group-mask (swb9-l-size))
        (swb9-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb9-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb9-address-p address)
     (let*
         ((group-field
           (swb9-l-group-balance-mask address))
          (group-mask
           (swb9-shift
            (swb9-pointer-memory
             (swb9-shift group-field 0))
            0)))
       (and
        (swb9-valid-rd-p group-field 1)
        (swb9-valid-rd-p group-mask (swb9-l-size))
        (swb9-separated-from-array-masks-p
         group-mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb9-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((cpu-field (swb9-l-cpu-smt-mask index))
          (cpu-mask
           (swb9-shift
            (swb9-pointer-memory
             (swb9-shift cpu-field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb9-l-size))
         (and
          (swb9-valid-rd-p cpu-field 1)
          (swb9-valid-rd-p cpu-mask (swb9-l-size))
          (swb9-separated-from-array-masks-p
           cpu-mask a))))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-7-goal9-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (swb9-function-types-p)
     (swb9-scheduler-schema-types-p)
     (swb9-zero-mask-memory-instance-p)
     (swb9-q-mask-refl-p)
     (swb9-q-mask-symm-p)
     (swb9-q-mask-trans-p)
     (integerp (swb9-l-size))
     (< 0 (swb9-l-size))
     (<= (swb9-l-size) 2147483647)
     (swb9-address-p a1)
     (integerp i)
     (swb9-address-p a))
    (let*
        ((a2 (swb9-shift a1 3))
         (a3 (swb9-shift a1 4))
         (a4 (swb9-pointer-memory a3))
         (a5
          (swb9-pointer-memory
           (swb9-shift a4 0)))
         (a6 (swb9-shift a1 1))
         (x (swb9-integer-memory a6))
         (x1
          (swb9-integer-memory
           (swb9-shift a5 x)))
         (a7 (swb9-shift a1 0))
         (a8
          (swb9-pointer-memory
           (swb9-shift a1 2)))
         (a9 (swb9-pointer-memory a7))
         (a10 (swb9-shift a9 0))
         (a11 (swb9-shift a5 0)))
      (implies
       (and
        (equal (swb9-integer-memory a2) 2)
        (not (equal x1 0))
        (<= 0 i)
        (< i (swb9-l-size))
        (<= 0 x)
        (< x (swb9-l-size))
        (<=
         (swb9-region (swb9-address-base a))
         0)
        (<=
         (swb9-region (swb9-address-base a1))
         0)
        (swb9-framed-p)
        (swb9-linked-p)
        (swb9-is-uint32-p i)
        (swb9-valid-rd-p a1 5)
        (swb9-is-sint32-p x)
        (swb9-valid-rd-p a3 1)
        (swb9-valid-rd-p a6 1)
        (swb9-valid-rd-p a2 1)
        (swb9-valid-rd-p a7 1)
        (swb9-valid-rd-p a4 1)
        (swb9-valid-rd-p a8 2)
        (swb9-valid-rd-p a9 2)
        (swb9-is-sint32-p
         (swb9-integer-memory
          (swb9-shift a9 1)))
        (swb9-valid-rd-p a10 1)
        (swb9-valid-rd-p
         (swb9-pointer-memory a10)
         1)
        (swb9-is-uint8-p x1)
        (swb9-valid-rd-p a11 (swb9-l-size))
        (swb9-separated-from-array-masks-p a11 a)
        (swb9-array-layout-p a)
        (swb9-sched-group-cpus-layout-p a)
        (swb9-sched-group-mask-layout-p a)
        (swb9-group-balance-mask-layout-p a)
        (swb9-cpu-smt-layout-p a))
       (swb9-valid-rd-p
        (swb9-shift a8 0)
        1))))))

(value-triple :itpeval-statement-checked)

:q
