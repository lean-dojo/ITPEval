;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_complete_not_newly_idle_without_idle_no____goal0:
;; the complete should-we-balance case split for newly idle and non-idle CPUs,
;; under the stated integer bounds, memory validity, framing, separation, and
;; CPU-mask layout hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swbc0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swbc0-address-base (address)
  (car address))

(defun swbc0-address-offset (address)
  (cdr address))

(defun swbc0-shift (address amount)
  (cons
   (swbc0-address-base address)
   (+ (swbc0-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source integer
;; memory t_1, pointer memory t_2, allocation map t, and the fixed source
;; symbols.

(defstub swbc0-integer-memory (address) t)
(defstub swbc0-pointer-memory (address) t)
(defstub swbc0-allocation (index) t)
(defstub swbc0-region (base) t)
(defstub swbc0-linked-op () t)
(defstub swbc0-l-size () t)
(defstub swbc0-mask-memory-apply (memory-symbol address) t)
(defstub swbc0-mask-pointer-apply (pointer-symbol address) t)
(defstub swbc0-l-idle-cpu (index) t)
(defstub swbc0-l-sched-group-cpus (address) t)
(defstub swbc0-l-sched-group-mask (address) t)
(defstub swbc0-l-group-balance-mask (address) t)
(defstub swbc0-l-cpu-smt-mask (index) t)

(defun swbc0-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swbc0-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swbc0-address-p address)
      (and
       (integerp
        (swbc0-mask-memory-apply
         memory-symbol address))
       (swbc0-address-p
        (swbc0-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swbc0-is-uint8-p
        (swbc0-l-idle-cpu index))
       (swbc0-address-p
        (swbc0-l-cpu-smt-mask index)))))))

(defun-sk swbc0-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swbc0-address-p address)
     (equal
      (swbc0-mask-memory-apply
       'swbc0-zero-memory address)
      0))))

(defun-sk swbc0-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swbc0-l-size)))
     (not
      (equal
       (swbc0-mask-memory-apply
        memory-symbol
        (swbc0-shift
         (swbc0-mask-pointer-apply
          pointer-symbol
          (swbc0-shift
           (swbc0-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swbc0-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swbc0-mask-memory-apply
         memory-symbol
         (swbc0-shift
          (swbc0-mask-pointer-apply
           pointer-symbol
           (swbc0-shift
            (swbc0-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swbc0-l-size))
      (<= 0 j)
      (< j (swbc0-l-size)))
     (not
      (equal
       (swbc0-mask-memory-apply
        memory-symbol
        (swbc0-shift
         (swbc0-mask-pointer-apply
          pointer-symbol
          (swbc0-shift
           (swbc0-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swbc0-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swbc0-mask-memory-apply
         memory-symbol
         (swbc0-shift
          (swbc0-mask-pointer-apply
           pointer-symbol
           (swbc0-shift
            (swbc0-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swbc0-mask-memory-apply
         memory-symbol
         (swbc0-shift
          (swbc0-mask-pointer-apply
           pointer-symbol
           (swbc0-shift
            (swbc0-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swbc0-l-size))
      (<= 0 j)
      (< j (swbc0-l-size))
      (<= 0 k)
      (< k (swbc0-l-size)))
     (not
      (equal
       (swbc0-mask-memory-apply
        memory-symbol
        (swbc0-shift
         (swbc0-mask-pointer-apply
          pointer-symbol
          (swbc0-shift
           (swbc0-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swbc0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swbc0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These clauses preserve the source function types over the full unbounded
;; integer and address domains. The uint8 clause is the imported idle-CPU
;; range property.

(defun-sk swbc0-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swbc0-address-p address)
      (and
       (integerp (swbc0-integer-memory address))
       (swbc0-address-p (swbc0-pointer-memory address))
       (swbc0-address-p
        (swbc0-l-sched-group-cpus address))
       (swbc0-address-p
        (swbc0-l-sched-group-mask address))
       (swbc0-address-p
        (swbc0-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swbc0-allocation index))
       (swbc0-is-uint8-p (swbc0-l-idle-cpu index))
       (swbc0-address-p (swbc0-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swbc0-region base))))))

(defun swbc0-linked-p ()
  (if (swbc0-linked-op) t nil))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swbc0-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swbc0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swbc0-address-base address))
    (<= 0 (swbc0-address-offset address))
    (<=
     (+ (swbc0-address-offset address) length)
     (swbc0-allocation (swbc0-address-base address))))))

(defun swbc0-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swbc0-address-base address)))
    (<= 0 (swbc0-address-offset address))
    (<=
     (+ (swbc0-address-offset address) length)
     (swbc0-allocation (swbc0-address-base address))))))

(defun swbc0-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swbc0-address-base left)
     (swbc0-address-base right)))
   (<=
    (+ (swbc0-address-offset right) right-length)
    (swbc0-address-offset left))
   (<=
    (+ (swbc0-address-offset left) left-length)
    (swbc0-address-offset right))))

;; Exact unfolding of Memory.framed for the arbitrary pointer memory t_2.

(defun-sk swbc0-framed-p ()
  (forall (address)
    (implies
     (swbc0-address-p address)
     (<=
      (swbc0-region
       (swbc0-address-base
        (swbc0-pointer-memory address)))
      0))))

;; Exact unfolding of p_idle_core for t_2 and t_1.

(defun-sk swbc0-idle-core-p (cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swbc0-integer-memory
         (swbc0-shift
          (swbc0-pointer-memory
           (swbc0-shift
            (swbc0-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swbc0-l-size))
        (not
         (equal
          (swbc0-l-idle-cpu index)
          0))))))))

;; Separation from every pointed-to mask in the source array.

(defun-sk swbc0-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swbc0-l-size))
       (swbc0-separated-p
        mask
        (swbc0-l-size)
        (swbc0-shift
         (swbc0-pointer-memory
          (swbc0-shift
           (swbc0-shift a index)
           0))
         0)
        (swbc0-l-size)))))))

;; The first quantified separation hypothesis for a_6.

(defun-sk swbc0-a6-separated-p (a6 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swbc0-l-size))
       (swbc0-separated-p
        a6
        (swbc0-l-size)
        (swbc0-shift
         (swbc0-pointer-memory
          (swbc0-shift
           (swbc0-shift a index)
           0))
         0)
        (swbc0-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swbc0-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((element (swbc0-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swbc0-l-size))
         (and
          (swbc0-valid-rd-p element 1)
          (swbc0-valid-rw-p
           (swbc0-shift
            (swbc0-pointer-memory
             (swbc0-shift element 0))
            0)
           (swbc0-l-size)))))))))

;; The three universally quantified group layout hypotheses.

(defun-sk swbc0-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swbc0-address-p address)
     (let*
         ((field (swbc0-l-sched-group-cpus address))
          (mask
           (swbc0-shift
            (swbc0-pointer-memory
             (swbc0-shift field 0))
            0)))
       (and
        (swbc0-valid-rd-p field 1)
        (swbc0-valid-rd-p mask (swbc0-l-size))
        (swbc0-separated-from-array-masks-p mask a))))))

(defun-sk swbc0-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swbc0-address-p address)
     (let*
         ((field (swbc0-l-sched-group-mask address))
          (mask
           (swbc0-shift
            (swbc0-pointer-memory
             (swbc0-shift field 0))
            0)))
       (and
        (swbc0-valid-rd-p field 1)
        (swbc0-valid-rd-p mask (swbc0-l-size))
        (swbc0-separated-from-array-masks-p mask a))))))

(defun-sk swbc0-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swbc0-address-p address)
     (let*
         ((field (swbc0-l-group-balance-mask address))
          (mask
           (swbc0-shift
            (swbc0-pointer-memory
             (swbc0-shift field 0))
            0)))
       (and
        (swbc0-valid-rd-p field 1)
        (swbc0-valid-rd-p mask (swbc0-l-size))
        (swbc0-separated-from-array-masks-p mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swbc0-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((field (swbc0-l-cpu-smt-mask index))
          (mask
           (swbc0-shift
            (swbc0-pointer-memory
             (swbc0-shift field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swbc0-l-size))
         (and
          (swbc0-valid-rd-p field 1)
          (swbc0-valid-rd-p mask (swbc0-l-size))
          (swbc0-separated-from-array-masks-p mask a))))))))

;; The universal and existential clauses used by the six-way conclusion.

(defun-sk swbc0-selected-cpus-idle-zero-p (a5 a7)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swbc0-integer-memory
         (swbc0-shift a5 index))
        0))
      (implies
       (not
        (equal
         (swbc0-integer-memory
          (swbc0-shift a7 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index (swbc0-l-size))
         (equal
          (swbc0-l-idle-cpu index)
          0))))))))

(defun-sk swbc0-selected-idle-core-exists-p (a5 a7)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swbc0-integer-memory
        (swbc0-shift a5 index))
       0))
     (not
      (equal
       (swbc0-integer-memory
        (swbc0-shift a7 index))
       0))
     (<= 0 index)
     (< index (swbc0-l-size))
     (swbc0-idle-core-p index))))

(defun-sk swbc0-selected-idle-cpu-exists-p (a5 a7)
  (exists (index)
    (and
     (integerp index)
     (not (equal (swbc0-l-idle-cpu index) 0))
     (not
      (equal
       (swbc0-integer-memory
        (swbc0-shift a5 index))
       0))
     (not
      (equal
       (swbc0-integer-memory
        (swbc0-shift a7 index))
       0))
     (<= 0 index)
     (< index (swbc0-l-size)))))

(defun-sk swbc0-selected-cpus-not-idle-core-p (a5 a7)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swbc0-integer-memory
         (swbc0-shift a5 index))
        0))
      (implies
       (not
        (equal
         (swbc0-integer-memory
          (swbc0-shift a7 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index (swbc0-l-size))
         (not
          (swbc0-idle-core-p index)))))))))

(defun swbc0-goal-body (a1 i a)
  (implies
   (and
    (swbc0-function-types-p)
    (swbc0-scheduler-schema-types-p)
    (swbc0-zero-mask-memory-instance-p)
    (swbc0-q-mask-refl-p)
    (swbc0-q-mask-symm-p)
    (swbc0-q-mask-trans-p)
    (integerp (swbc0-l-size))
    (< 0 (swbc0-l-size))
    (<= (swbc0-l-size) 2147483647)
    (swbc0-address-p a1)
    (integerp i)
    (swbc0-address-p a))
   (let*
       ((x
         (swbc0-integer-memory
          (swbc0-shift a1 1)))
        (x1
         (swbc0-integer-memory
          (swbc0-shift a1 3)))
        (a2
         (swbc0-pointer-memory
          (swbc0-shift a1 4)))
        (a3
         (swbc0-pointer-memory
          (swbc0-shift a1 0)))
        (x2
         (swbc0-integer-memory
          (swbc0-shift a3 1)))
        (a4
         (swbc0-pointer-memory
          (swbc0-shift a3 0)))
        (a5
         (swbc0-pointer-memory
          (swbc0-shift a2 0)))
        (x3
         (swbc0-integer-memory
          (swbc0-shift a5 x)))
        (a6 (swbc0-shift a5 0))
        (a7
         (swbc0-pointer-memory
          (swbc0-shift
           (swbc0-l-group-balance-mask a4)
           0)))
        (x4 (swbc0-land 7 x2)))
     (implies
      (and
       (<= 0 i)
       (< i (swbc0-l-size))
       (<= 0 x)
       (< x (swbc0-l-size))
       (<= (swbc0-region (swbc0-address-base a)) 0)
       (<= (swbc0-region (swbc0-address-base a1)) 0)
       (swbc0-framed-p)
       (swbc0-linked-p)
       (swbc0-is-uint32-p i)
       (swbc0-valid-rd-p a1 5)
       (swbc0-is-uint32-p x1)
       (swbc0-is-sint32-p x)
       (swbc0-valid-rd-p a2 1)
       (swbc0-valid-rd-p
        (swbc0-pointer-memory
         (swbc0-shift a1 2))
        2)
       (swbc0-valid-rd-p a3 2)
       (swbc0-is-sint32-p x2)
       (swbc0-valid-rd-p a4 1)
       (swbc0-is-uint8-p x3)
       (swbc0-valid-rd-p a6 (swbc0-l-size))
       (swbc0-a6-separated-p a6 a)
       (swbc0-array-layout-p a)
       (swbc0-sched-group-cpus-layout-p a)
       (swbc0-sched-group-mask-layout-p a)
       (swbc0-group-balance-mask-layout-p a)
       (swbc0-cpu-smt-layout-p a))
      (or
       (equal x3 0)
       (and
        (equal x1 2)
        (not (equal x3 0)))
       (and
        (not (equal x1 2))
        (not (equal x3 0))
        (swbc0-selected-cpus-idle-zero-p a5 a7))
       (and
        (not (equal x1 2))
        (equal x4 0)
        (not (equal x3 0))
        (swbc0-selected-idle-core-exists-p a5 a7))
       (and
        (not (equal x1 2))
        (not (equal x4 0))
        (not (equal x3 0))
        (swbc0-selected-idle-cpu-exists-p a5 a7))
       (and
        (not (equal x1 2))
        (equal x4 0)
        (not (equal x3 0))
        (swbc0-selected-cpus-not-idle-core-p a5 a7)
        (swbc0-selected-idle-cpu-exists-p a5 a7)))))))

(defun-sk
    ntp4vc-should-we-balance-complete-not-newly-idle-without-idle-no-goal0-statement
    ()
  (forall (a1 i a)
    (swbc0-goal-body a1 i a)))

(value-triple :itpeval-statement-checked)

:q
