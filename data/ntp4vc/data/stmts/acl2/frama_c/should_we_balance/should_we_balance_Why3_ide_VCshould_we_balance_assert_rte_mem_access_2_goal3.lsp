;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_2_goal3:
;; readability of an intermediate scheduling pointer under the stated integer
;; ranges, memory validity, framing, separation, and CPU-mask layout
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb3-address-base (address)
  (car address))

(defun swb3-address-offset (address)
  (cdr address))

(defun swb3-shift (address amount)
  (cons
   (swb3-address-base address)
   (+ (swb3-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source integer memory t_1,
;; pointer memory t_2, allocation map t, and the fixed source symbols.

(defstub swb3-integer-memory (address) t)
(defstub swb3-pointer-memory (address) t)
(defstub swb3-allocation (index) t)
(defstub swb3-region (base) t)
(defstub swb3-linked-op () t)
(defstub swb3-l-size () t)
(defstub swb3-l-idle-cpu (index) t)
(defstub swb3-mask-memory-apply (memory-symbol address) t)
(defstub swb3-mask-pointer-apply (pointer-symbol address) t)
(defstub swb3-l-sched-group-cpus (address) t)
(defstub swb3-l-sched-group-mask (address) t)
(defstub swb3-l-group-balance-mask (address) t)
(defstub swb3-l-cpu-smt-mask (index) t)

(defun swb3-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb3-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb3-address-p address)
      (and
       (integerp
        (swb3-mask-memory-apply
         memory-symbol address))
       (swb3-address-p
        (swb3-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb3-is-uint8-p
        (swb3-l-idle-cpu index))
       (swb3-address-p
        (swb3-l-cpu-smt-mask index)))))))

(defun-sk swb3-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb3-address-p address)
     (equal
      (swb3-mask-memory-apply
       'swb3-zero-memory address)
      0))))

(defun-sk swb3-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb3-l-size)))
     (not
      (equal
       (swb3-mask-memory-apply
        memory-symbol
        (swb3-shift
         (swb3-mask-pointer-apply
          pointer-symbol
          (swb3-shift
           (swb3-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb3-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb3-mask-memory-apply
         memory-symbol
         (swb3-shift
          (swb3-mask-pointer-apply
           pointer-symbol
           (swb3-shift
            (swb3-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb3-l-size))
      (<= 0 j)
      (< j (swb3-l-size)))
     (not
      (equal
       (swb3-mask-memory-apply
        memory-symbol
        (swb3-shift
         (swb3-mask-pointer-apply
          pointer-symbol
          (swb3-shift
           (swb3-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb3-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb3-mask-memory-apply
         memory-symbol
         (swb3-shift
          (swb3-mask-pointer-apply
           pointer-symbol
           (swb3-shift
            (swb3-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb3-mask-memory-apply
         memory-symbol
         (swb3-shift
          (swb3-mask-pointer-apply
           pointer-symbol
           (swb3-shift
            (swb3-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb3-l-size))
      (<= 0 j)
      (< j (swb3-l-size))
      (<= 0 k)
      (< k (swb3-l-size)))
     (not
      (equal
       (swb3-mask-memory-apply
        memory-symbol
        (swb3-shift
         (swb3-mask-pointer-apply
          pointer-symbol
          (swb3-shift
           (swb3-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb3-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are exactly the source function types, expressed over the full
;; unbounded integer and address domains.

(defun-sk swb3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb3-address-p address)
      (and
       (integerp (swb3-integer-memory address))
       (swb3-address-p (swb3-pointer-memory address))
       (swb3-address-p
        (swb3-l-sched-group-cpus address))
       (swb3-address-p
        (swb3-l-sched-group-mask address))
       (swb3-address-p
        (swb3-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb3-allocation index))
       (swb3-address-p (swb3-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb3-region base))))))

(defun swb3-linked-p ()
  (if (swb3-linked-op) t nil))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb3-address-base address))
    (<= 0 (swb3-address-offset address))
    (<=
     (+ (swb3-address-offset address) length)
     (swb3-allocation (swb3-address-base address))))))

(defun swb3-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb3-address-base address)))
    (<= 0 (swb3-address-offset address))
    (<=
     (+ (swb3-address-offset address) length)
     (swb3-allocation (swb3-address-base address))))))

(defun swb3-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb3-address-base left)
     (swb3-address-base right)))
   (<=
    (+ (swb3-address-offset right) right-length)
    (swb3-address-offset left))
   (<=
    (+ (swb3-address-offset left) left-length)
    (swb3-address-offset right))))

;; Exact unfolding of Memory.framed for t_2.

(defun-sk swb3-framed-p ()
  (forall (address)
    (implies
     (swb3-address-p address)
     (<=
      (swb3-region
       (swb3-address-base
        (swb3-pointer-memory address)))
      0))))

;; Separation from every pointed-to mask in the source array.

(defun-sk swb3-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb3-l-size))
       (swb3-separated-p
        mask
        (swb3-l-size)
        (swb3-shift
         (swb3-pointer-memory
          (swb3-shift
           (swb3-shift a index)
           0))
         0)
        (swb3-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb3-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((array-entry (swb3-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb3-l-size))
         (and
          (swb3-valid-rd-p array-entry 1)
          (swb3-valid-rw-p
           (swb3-shift
            (swb3-pointer-memory
             (swb3-shift array-entry 0))
            0)
           (swb3-l-size)))))))))

;; The three address-indexed scheduling layouts from the source hypotheses.

(defun-sk swb3-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb3-address-p address)
     (let*
         ((group-field
           (swb3-l-sched-group-cpus address))
          (group-mask
           (swb3-shift
            (swb3-pointer-memory
             (swb3-shift group-field 0))
            0)))
       (and
        (swb3-valid-rd-p group-field 1)
        (swb3-valid-rd-p group-mask (swb3-l-size))
        (swb3-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb3-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb3-address-p address)
     (let*
         ((group-field
           (swb3-l-sched-group-mask address))
          (group-mask
           (swb3-shift
            (swb3-pointer-memory
             (swb3-shift group-field 0))
            0)))
       (and
        (swb3-valid-rd-p group-field 1)
        (swb3-valid-rd-p group-mask (swb3-l-size))
        (swb3-separated-from-array-masks-p
         group-mask a))))))

(defun-sk swb3-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb3-address-p address)
     (let*
         ((group-field
           (swb3-l-group-balance-mask address))
          (group-mask
           (swb3-shift
            (swb3-pointer-memory
             (swb3-shift group-field 0))
            0)))
       (and
        (swb3-valid-rd-p group-field 1)
        (swb3-valid-rd-p group-mask (swb3-l-size))
        (swb3-separated-from-array-masks-p
         group-mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb3-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((cpu-field (swb3-l-cpu-smt-mask index))
          (cpu-mask
           (swb3-shift
            (swb3-pointer-memory
             (swb3-shift cpu-field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb3-l-size))
         (and
          (swb3-valid-rd-p cpu-field 1)
          (swb3-valid-rd-p cpu-mask (swb3-l-size))
          (swb3-separated-from-array-masks-p
           cpu-mask a))))))))

(defun-sk
    ntp4vc-should-we-balance-assert-rte-mem-access-2-goal3-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (swb3-function-types-p)
     (swb3-scheduler-schema-types-p)
     (swb3-zero-mask-memory-instance-p)
     (swb3-q-mask-refl-p)
     (swb3-q-mask-symm-p)
     (swb3-q-mask-trans-p)
     (integerp (swb3-l-size))
     (< 0 (swb3-l-size))
     (<= (swb3-l-size) 2147483647)
     (swb3-address-p a1)
     (integerp i)
     (swb3-address-p a))
    (let*
        ((x
          (swb3-integer-memory
           (swb3-shift a1 1)))
         (a2
          (swb3-pointer-memory
           (swb3-shift a1 4)))
         (a3
          (swb3-pointer-memory
           (swb3-shift a1 0)))
         (a4 (swb3-shift a3 0))
         (a5
          (swb3-pointer-memory
           (swb3-shift a2 0)))
         (a6 (swb3-shift a5 0)))
      (implies
       (and
        (<= 0 i)
        (< i (swb3-l-size))
        (<= 0 x)
        (< x (swb3-l-size))
        (<=
         (swb3-region (swb3-address-base a))
         0)
        (<=
         (swb3-region (swb3-address-base a1))
         0)
        (swb3-framed-p)
        (swb3-linked-p)
        (swb3-is-uint32-p i)
        (swb3-valid-rd-p a1 5)
        (swb3-is-uint32-p
         (swb3-integer-memory
          (swb3-shift a1 3)))
        (swb3-is-sint32-p x)
        (swb3-valid-rd-p a2 1)
        (swb3-valid-rd-p
         (swb3-pointer-memory
          (swb3-shift a1 2))
         2)
        (swb3-valid-rd-p a3 2)
        (swb3-is-sint32-p
         (swb3-integer-memory
          (swb3-shift a3 1)))
        (swb3-valid-rd-p
         (swb3-pointer-memory a4)
         1)
        (swb3-is-uint8-p
         (swb3-integer-memory
          (swb3-shift a5 x)))
        (swb3-valid-rd-p a6 (swb3-l-size))
        (swb3-separated-from-array-masks-p a6 a)
        (swb3-array-layout-p a)
        (swb3-sched-group-cpus-layout-p a)
        (swb3-sched-group-mask-layout-p a)
        (swb3-group-balance-mask-layout-p a)
        (swb3-cpu-smt-layout-p a))
       (swb3-valid-rd-p a4 1))))))

(value-triple :itpeval-statement-checked)

:q
