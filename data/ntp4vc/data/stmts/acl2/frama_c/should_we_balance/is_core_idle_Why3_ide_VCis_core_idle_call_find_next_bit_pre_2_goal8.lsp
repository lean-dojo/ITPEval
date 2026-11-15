;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_call_find_next_bit_pre_2_goal8:
;; validity of reading a CPU SMT mask after the stated integer bounds, memory
;; validity, framing, linking, idle-CPU, group-mask, and separation hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun icg8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun icg8-address-base (address)
  (car address))

(defun icg8-address-offset (address)
  (cdr address))

(defun icg8-shift (address amount)
  (cons
   (icg8-address-base address)
   (+ (icg8-address-offset address) amount)))

;; Conservative interfaces for the arbitrary pointer memory t_2, allocation
;; map t, byte/integer memory t_1, and the fixed source symbols.

(defstub icg8-pointer-memory (address) t)
(defstub icg8-allocation (index) t)
(defstub icg8-integer-memory (address) t)
(defstub icg8-region (base) t)
(defstub icg8-linked-op () t)
(defstub icg8-l-size () t)
(defstub icg8-mask-memory-apply (memory-symbol address) t)
(defstub icg8-mask-pointer-apply (pointer-symbol address) t)
(defstub icg8-l-idle-cpu (index) t)
(defstub icg8-l-sched-group-cpus (address) t)
(defstub icg8-l-sched-group-mask (address) t)
(defstub icg8-l-group-balance-mask (address) t)
(defstub icg8-l-cpu-smt-mask (index) t)

(defun icg8-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk icg8-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (icg8-address-p address)
      (and
       (integerp
        (icg8-mask-memory-apply
         memory-symbol address))
       (icg8-address-p
        (icg8-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (icg8-is-uint8-p
        (icg8-l-idle-cpu index))
       (icg8-address-p
        (icg8-l-cpu-smt-mask index)))))))

(defun-sk icg8-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (icg8-address-p address)
     (equal
      (icg8-mask-memory-apply
       'icg8-zero-memory address)
      0))))

(defun-sk icg8-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (icg8-l-size)))
     (not
      (equal
       (icg8-mask-memory-apply
        memory-symbol
        (icg8-shift
         (icg8-mask-pointer-apply
          pointer-symbol
          (icg8-shift
           (icg8-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk icg8-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (icg8-mask-memory-apply
         memory-symbol
         (icg8-shift
          (icg8-mask-pointer-apply
           pointer-symbol
           (icg8-shift
            (icg8-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (icg8-l-size))
      (<= 0 j)
      (< j (icg8-l-size)))
     (not
      (equal
       (icg8-mask-memory-apply
        memory-symbol
        (icg8-shift
         (icg8-mask-pointer-apply
          pointer-symbol
          (icg8-shift
           (icg8-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk icg8-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (icg8-mask-memory-apply
         memory-symbol
         (icg8-shift
          (icg8-mask-pointer-apply
           pointer-symbol
           (icg8-shift
            (icg8-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (icg8-mask-memory-apply
         memory-symbol
         (icg8-shift
          (icg8-mask-pointer-apply
           pointer-symbol
           (icg8-shift
            (icg8-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (icg8-l-size))
      (<= 0 j)
      (< j (icg8-l-size))
      (<= 0 k)
      (< k (icg8-l-size)))
     (not
      (equal
       (icg8-mask-memory-apply
        memory-symbol
        (icg8-shift
         (icg8-mask-pointer-apply
          pointer-symbol
          (icg8-shift
           (icg8-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun-sk icg8-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (icg8-address-p address)
      (and
       (icg8-address-p (icg8-pointer-memory address))
       (integerp (icg8-integer-memory address))
       (icg8-address-p (icg8-l-sched-group-cpus address))
       (icg8-address-p (icg8-l-sched-group-mask address))
       (icg8-address-p (icg8-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (icg8-allocation index))
       (icg8-is-uint8-p (icg8-l-idle-cpu index))
       (icg8-address-p (icg8-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (icg8-region base))))))

(defun icg8-linked-p ()
  (if (icg8-linked-op) t nil))

(defun icg8-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun icg8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun icg8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (icg8-address-base address))
    (<= 0 (icg8-address-offset address))
    (<=
     (+ (icg8-address-offset address) length)
     (icg8-allocation (icg8-address-base address))))))

(defun icg8-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (icg8-address-base address)))
    (<= 0 (icg8-address-offset address))
    (<=
     (+ (icg8-address-offset address) length)
     (icg8-allocation (icg8-address-base address))))))

(defun icg8-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (icg8-address-base left)
     (icg8-address-base right)))
   (<=
    (+ (icg8-address-offset right) right-length)
    (icg8-address-offset left))
   (<=
    (+ (icg8-address-offset left) left-length)
    (icg8-address-offset right))))

;; Exact unfolding of Memory.framed for t_2.

(defun-sk icg8-framed-p ()
  (forall (address)
    (implies
     (icg8-address-p address)
     (<=
      (icg8-region
       (icg8-address-base
        (icg8-pointer-memory address)))
      0))))

;; The first quantified source hypothesis: every selected CPU below i_1 is
;; non-idle.

(defun-sk icg8-selected-cpus-non-idle-p (a2 i1)
  (forall (i3)
    (implies
     (integerp i3)
     (implies
      (not
       (equal
        (icg8-integer-memory
         (icg8-shift a2 i3))
        0))
      (implies
       (<= 0 i3)
       (implies
        (< i3 i1)
        (not
         (equal
          (icg8-l-idle-cpu i3)
          0))))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk icg8-array-layout-p (a)
  (forall (i3)
    (implies
     (integerp i3)
     (let ((a3 (icg8-shift a i3)))
       (implies
        (<= 0 i3)
        (implies
         (< i3 (icg8-l-size))
         (and
          (icg8-valid-rd-p a3 1)
          (icg8-valid-rw-p
           (icg8-shift
            (icg8-pointer-memory
             (icg8-shift a3 0))
            0)
           (icg8-l-size)))))))))

;; The separation clause shared by the three group-mask hypotheses.

(defun-sk icg8-separated-from-array-masks-p (mask a)
  (forall (i3)
    (implies
     (integerp i3)
     (implies
      (<= 0 i3)
      (implies
       (< i3 (icg8-l-size))
       (icg8-separated-p
        mask
        (icg8-l-size)
        (icg8-shift
         (icg8-pointer-memory
          (icg8-shift
           (icg8-shift a i3)
           0))
         0)
        (icg8-l-size)))))))

(defun-sk icg8-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (icg8-address-p address)
     (let*
         ((a4 (icg8-l-sched-group-cpus address))
          (a5
           (icg8-shift
            (icg8-pointer-memory
             (icg8-shift a4 0))
            0)))
       (and
        (icg8-valid-rd-p a4 1)
        (icg8-valid-rd-p a5 (icg8-l-size))
        (icg8-separated-from-array-masks-p a5 a))))))

(defun-sk icg8-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (icg8-address-p address)
     (let*
         ((a4 (icg8-l-sched-group-mask address))
          (a5
           (icg8-shift
            (icg8-pointer-memory
             (icg8-shift a4 0))
            0)))
       (and
        (icg8-valid-rd-p a4 1)
        (icg8-valid-rd-p a5 (icg8-l-size))
        (icg8-separated-from-array-masks-p a5 a))))))

(defun-sk icg8-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (icg8-address-p address)
     (let*
         ((a4 (icg8-l-group-balance-mask address))
          (a5
           (icg8-shift
            (icg8-pointer-memory
             (icg8-shift a4 0))
            0)))
       (and
        (icg8-valid-rd-p a4 1)
        (icg8-valid-rd-p a5 (icg8-l-size))
        (icg8-separated-from-array-masks-p a5 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk icg8-cpu-smt-layout-p (a)
  (forall (i3)
    (implies
     (integerp i3)
     (let*
         ((a3 (icg8-l-cpu-smt-mask i3))
          (a4
           (icg8-shift
            (icg8-pointer-memory
             (icg8-shift a3 0))
            0)))
       (implies
        (<= 0 i3)
        (implies
         (< i3 (icg8-l-size))
         (and
          (icg8-valid-rd-p a3 1)
          (icg8-valid-rd-p a4 (icg8-l-size))
          (icg8-separated-from-array-masks-p a4 a))))))))

(defun-sk
    ntp4vc-is-core-idle-call-find-next-bit-pre-2-goal8-statement ()
  (forall
   (i2 i i1 a)
   (implies
    (and
     (icg8-function-types-p)
     (icg8-scheduler-schema-types-p)
     (icg8-zero-mask-memory-instance-p)
     (icg8-q-mask-refl-p)
     (icg8-q-mask-symm-p)
     (icg8-q-mask-trans-p)
     (integerp (icg8-l-size))
     (< 0 (icg8-l-size))
     (<= (icg8-l-size) 2147483647)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (icg8-address-p a))
    (let*
        ((a1
          (icg8-shift
           (icg8-l-cpu-smt-mask i2)
           0))
         (a2 (icg8-pointer-memory a1)))
      (implies
       (and
        (not (equal (icg8-l-idle-cpu i2) 0))
        (<= 0 i)
        (< i (icg8-l-size))
        (<= 0 i1)
        (<= 0 i2)
        (< i2 (icg8-l-size))
        (<= i1 (icg8-l-size))
        (<= (icg8-region (icg8-address-base a)) 0)
        (icg8-framed-p)
        (icg8-linked-p)
        (icg8-is-uint32-p i)
        (icg8-is-sint32-p i1)
        (icg8-is-sint32-p i2)
        (icg8-valid-rd-p a1 1)
        (icg8-selected-cpus-non-idle-p a2 i1)
        (icg8-array-layout-p a)
        (icg8-sched-group-cpus-layout-p a)
        (icg8-sched-group-mask-layout-p a)
        (icg8-group-balance-mask-layout-p a)
        (icg8-cpu-smt-layout-p a))
       (icg8-valid-rd-p
        (icg8-shift a2 0)
        (icg8-l-size)))))))

(value-triple :itpeval-statement-checked)

:q
