;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_4_goal5:
;; readability of the scheduling-structure field at offset four under the
;; stated integer ranges, memory validity, framing, separation, and CPU-mask
;; layout hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb5-address-base (address)
  (car address))

(defun swb5-address-offset (address)
  (cdr address))

(defun swb5-shift (address amount)
  (cons
   (swb5-address-base address)
   (+ (swb5-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source integer memory t_1,
;; pointer memory t_2, allocation map t, and the fixed source symbols.

(defstub swb5-integer-memory (address) t)
(defstub swb5-pointer-memory (address) t)
(defstub swb5-allocation (index) t)
(defstub swb5-region (base) t)
(defstub swb5-linked-op () t)
(defstub swb5-l-size () t)
(defstub swb5-l-idle-cpu (index) t)
(defstub swb5-mask-memory-apply (memory-symbol address) t)
(defstub swb5-mask-pointer-apply (pointer-symbol address) t)
(defstub swb5-l-sched-group-cpus (address) t)
(defstub swb5-l-sched-group-mask (address) t)
(defstub swb5-l-group-balance-mask (address) t)
(defstub swb5-l-cpu-smt-mask (index) t)

(defun swb5-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb5-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb5-address-p address)
      (and
       (integerp
        (swb5-mask-memory-apply
         memory-symbol address))
       (swb5-address-p
        (swb5-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb5-is-uint8-p
        (swb5-l-idle-cpu index))
       (swb5-address-p
        (swb5-l-cpu-smt-mask index)))))))

(defun-sk swb5-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb5-address-p address)
     (equal
      (swb5-mask-memory-apply
       'swb5-zero-memory address)
      0))))

(defun-sk swb5-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb5-l-size)))
     (not
      (equal
       (swb5-mask-memory-apply
        memory-symbol
        (swb5-shift
         (swb5-mask-pointer-apply
          pointer-symbol
          (swb5-shift
           (swb5-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb5-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb5-mask-memory-apply
         memory-symbol
         (swb5-shift
          (swb5-mask-pointer-apply
           pointer-symbol
           (swb5-shift
            (swb5-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb5-l-size))
      (<= 0 j)
      (< j (swb5-l-size)))
     (not
      (equal
       (swb5-mask-memory-apply
        memory-symbol
        (swb5-shift
         (swb5-mask-pointer-apply
          pointer-symbol
          (swb5-shift
           (swb5-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb5-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb5-mask-memory-apply
         memory-symbol
         (swb5-shift
          (swb5-mask-pointer-apply
           pointer-symbol
           (swb5-shift
            (swb5-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb5-mask-memory-apply
         memory-symbol
         (swb5-shift
          (swb5-mask-pointer-apply
           pointer-symbol
           (swb5-shift
            (swb5-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb5-l-size))
      (<= 0 j)
      (< j (swb5-l-size))
      (<= 0 k)
      (< k (swb5-l-size)))
     (not
      (equal
       (swb5-mask-memory-apply
        memory-symbol
        (swb5-shift
         (swb5-mask-pointer-apply
          pointer-symbol
          (swb5-shift
           (swb5-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb5-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are exactly the source function types, expressed over the full
;; unbounded integer and address domains.

(defun-sk swb5-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb5-address-p address)
      (and
       (integerp (swb5-integer-memory address))
       (swb5-address-p (swb5-pointer-memory address))
       (swb5-address-p
        (swb5-l-sched-group-cpus address))
       (swb5-address-p
        (swb5-l-sched-group-mask address))
       (swb5-address-p
        (swb5-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb5-allocation index))
       (swb5-address-p (swb5-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb5-region base))))))

(defun swb5-linked-p ()
  (if (swb5-linked-op) t nil))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb5-address-base address))
    (<= 0 (swb5-address-offset address))
    (<=
     (+ (swb5-address-offset address) length)
     (swb5-allocation (swb5-address-base address))))))

(defun swb5-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb5-address-base address)))
    (<= 0 (swb5-address-offset address))
    (<=
     (+ (swb5-address-offset address) length)
     (swb5-allocation (swb5-address-base address))))))

(defun swb5-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb5-address-base left)
     (swb5-address-base right)))
   (<=
    (+ (swb5-address-offset right) right-length)
    (swb5-address-offset left))
   (<=
    (+ (swb5-address-offset left) left-length)
    (swb5-address-offset right))))

;; Exact unfolding of Memory.framed for t_2.

(defun-sk swb5-framed-p ()
  (forall (address)
    (implies
     (swb5-address-p address)
     (<=
      (swb5-region
       (swb5-address-base
        (swb5-pointer-memory address)))
      0))))

;; Separation from every pointed-to mask in the source array.

(defun-sk swb5-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb5-l-size))
       (swb5-separated-p
        mask
        (swb5-l-size)
        (swb5-shift
         (swb5-pointer-memory
          (swb5-shift
           (swb5-shift a index)
           0))
         0)
        (swb5-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb5-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((array-entry (swb5-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb5-l-size))
         (and
          (swb5-valid-rd-p array-entry 1)
          (swb5-valid-rw-p
           (swb5-shift
            (swb5-pointer-memory
             (swb5-shift array-entry 0))
            0)
           (swb5-l-size)))))))))

;; The three address-indexed scheduling layouts from the source hypotheses.

(defun-sk swb5-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb5-address-p address)
     (let*
         ((group-field
           (swb5-l-sched-group-cpus address))
          (group-mask
           (swb5-shift
            (swb5-pointer-memory
             (swb5-shift group-field 0))
            0)))
       (and
        (swb5-valid-rd-p group-field 1)
        (swb5-valid-rd-p group-mask (swb5-l-size))
        (swb5-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb5-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb5-address-p address)
     (let*
         ((group-field
           (swb5-l-sched-group-mask address))
          (group-mask
           (swb5-shift
            (swb5-pointer-memory
             (swb5-shift group-field 0))
            0)))
       (and
        (swb5-valid-rd-p group-field 1)
        (swb5-valid-rd-p group-mask (swb5-l-size))
        (swb5-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb5-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb5-address-p address)
     (let*
         ((group-field
           (swb5-l-group-balance-mask address))
          (group-mask
           (swb5-shift
            (swb5-pointer-memory
             (swb5-shift group-field 0))
            0)))
       (and
        (swb5-valid-rd-p group-field 1)
        (swb5-valid-rd-p group-mask (swb5-l-size))
        (swb5-separated-from-array-masks-p
         group-mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb5-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((cpu-field (swb5-l-cpu-smt-mask index))
          (cpu-mask
           (swb5-shift
            (swb5-pointer-memory
             (swb5-shift cpu-field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb5-l-size))
         (and
          (swb5-valid-rd-p cpu-field 1)
          (swb5-valid-rd-p cpu-mask (swb5-l-size))
          (swb5-separated-from-array-masks-p
           cpu-mask a))))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-4-goal5-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (swb5-function-types-p)
     (swb5-scheduler-schema-types-p)
     (swb5-zero-mask-memory-instance-p)
     (swb5-q-mask-refl-p)
     (swb5-q-mask-symm-p)
     (swb5-q-mask-trans-p)
     (integerp (swb5-l-size))
     (< 0 (swb5-l-size))
     (<= (swb5-l-size) 2147483647)
     (swb5-address-p a1)
     (integerp i)
     (swb5-address-p a))
    (let*
        ((x
          (swb5-integer-memory
           (swb5-shift a1 1)))
         (a2 (swb5-shift a1 0))
         (a3 (swb5-shift a1 4))
         (a4 (swb5-pointer-memory a3))
         (a5 (swb5-pointer-memory a2))
         (a6 (swb5-shift a5 0))
         (a7
          (swb5-pointer-memory
           (swb5-shift a4 0)))
         (a8 (swb5-shift a7 0)))
      (implies
       (and
        (<= 0 i)
        (< i (swb5-l-size))
        (<= 0 x)
        (< x (swb5-l-size))
        (<=
         (swb5-region (swb5-address-base a))
         0)
        (<=
         (swb5-region (swb5-address-base a1))
         0)
        (swb5-framed-p)
        (swb5-linked-p)
        (swb5-is-uint32-p i)
        (swb5-valid-rd-p a1 5)
        (swb5-is-uint32-p
         (swb5-integer-memory
          (swb5-shift a1 3)))
        (swb5-is-sint32-p x)
        (swb5-valid-rd-p a2 1)
        (swb5-valid-rd-p a4 1)
        (swb5-valid-rd-p
         (swb5-pointer-memory
          (swb5-shift a1 2))
         2)
        (swb5-valid-rd-p a5 2)
        (swb5-is-sint32-p
         (swb5-integer-memory
          (swb5-shift a5 1)))
        (swb5-valid-rd-p a6 1)
        (swb5-valid-rd-p
         (swb5-pointer-memory a6)
         1)
        (swb5-is-uint8-p
         (swb5-integer-memory
          (swb5-shift a7 x)))
        (swb5-valid-rd-p a8 (swb5-l-size))
        (swb5-separated-from-array-masks-p a8 a)
        (swb5-array-layout-p a)
        (swb5-sched-group-cpus-layout-p a)
        (swb5-sched-group-mask-layout-p a)
        (swb5-group-balance-mask-layout-p a)
        (swb5-cpu-smt-layout-p a))
       (swb5-valid-rd-p a3 1))))))

(value-triple :itpeval-statement-checked)

:q
