;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_preserved_goal11:
;; preservation of the lower-bound loop invariant for the current CPU index
;; under integer bounds, memory validity, framing, separation, havoc-memory
;; agreement, and quantified scheduling and CPU-mask layout hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb11-address-base (address)
  (car address))

(defun swb11-address-offset (address)
  (cdr address))

(defun swb11-shift (address amount)
  (cons
   (swb11-address-base address)
   (+ (swb11-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source integer memories t_1,
;; t_2, t_3, t_4, pointer memory t_5, allocation map t, and fixed symbols.

(defstub swb11-t1 (address) t)
(defstub swb11-t2 (address) t)
(defstub swb11-t3 (address) t)
(defstub swb11-t4 (address) t)
(defstub swb11-t5 (address) t)
(defstub swb11-allocation (index) t)
(defstub swb11-region (base) t)
(defstub swb11-linked-op () t)
(defstub swb11-l-size () t)
(defstub swb11-mask-memory-apply (memory-symbol address) t)
(defstub swb11-mask-pointer-apply (pointer-symbol address) t)
(defstub swb11-l-idle-cpu (index) t)
(defstub swb11-l-sched-group-cpus (address) t)
(defstub swb11-l-sched-group-mask (address) t)
(defstub swb11-l-group-balance-mask (address) t)
(defstub swb11-l-cpu-smt-mask (index) t)

(defun swb11-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb11-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb11-address-p address)
      (and
       (integerp
        (swb11-mask-memory-apply
         memory-symbol address))
       (swb11-address-p
        (swb11-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb11-is-uint8-p
        (swb11-l-idle-cpu index))
       (swb11-address-p
        (swb11-l-cpu-smt-mask index)))))))

(defun-sk swb11-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb11-address-p address)
     (equal
      (swb11-mask-memory-apply
       'swb11-zero-memory address)
      0))))

(defun-sk swb11-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb11-l-size)))
     (not
      (equal
       (swb11-mask-memory-apply
        memory-symbol
        (swb11-shift
         (swb11-mask-pointer-apply
          pointer-symbol
          (swb11-shift
           (swb11-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb11-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb11-mask-memory-apply
         memory-symbol
         (swb11-shift
          (swb11-mask-pointer-apply
           pointer-symbol
           (swb11-shift
            (swb11-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb11-l-size))
      (<= 0 j)
      (< j (swb11-l-size)))
     (not
      (equal
       (swb11-mask-memory-apply
        memory-symbol
        (swb11-shift
         (swb11-mask-pointer-apply
          pointer-symbol
          (swb11-shift
           (swb11-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb11-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb11-mask-memory-apply
         memory-symbol
         (swb11-shift
          (swb11-mask-pointer-apply
           pointer-symbol
           (swb11-shift
            (swb11-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb11-mask-memory-apply
         memory-symbol
         (swb11-shift
          (swb11-mask-pointer-apply
           pointer-symbol
           (swb11-shift
            (swb11-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb11-l-size))
      (<= 0 j)
      (< j (swb11-l-size))
      (<= 0 k)
      (< k (swb11-l-size)))
     (not
      (equal
       (swb11-mask-memory-apply
        memory-symbol
        (swb11-shift
         (swb11-mask-pointer-apply
          pointer-symbol
          (swb11-shift
           (swb11-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb11-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Preserve every source function type over the full unbounded integer and
;; address domains, together with the imported idle-CPU range property.

(defun-sk swb11-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb11-address-p address)
      (and
       (integerp (swb11-t1 address))
       (integerp (swb11-t2 address))
       (integerp (swb11-t3 address))
       (integerp (swb11-t4 address))
       (swb11-address-p (swb11-t5 address))
       (swb11-address-p
        (swb11-l-sched-group-cpus address))
       (swb11-address-p
        (swb11-l-sched-group-mask address))
       (swb11-address-p
        (swb11-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb11-allocation index))
       (swb11-is-uint8-p (swb11-l-idle-cpu index))
       (swb11-address-p (swb11-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb11-region base))))))

(defun swb11-linked-p ()
  (if (swb11-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun swb11-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Cbits.land is mathematical bitwise conjunction on integers.

(defun swb11-land (left right)
  (logand left right))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb11-address-base address))
    (<= 0 (swb11-address-offset address))
    (<=
     (+ (swb11-address-offset address) length)
     (swb11-allocation (swb11-address-base address))))))

(defun swb11-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb11-address-base address)))
    (<= 0 (swb11-address-offset address))
    (<=
     (+ (swb11-address-offset address) length)
     (swb11-allocation (swb11-address-base address))))))

(defun swb11-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb11-address-base left)
     (swb11-address-base right)))
   (<=
    (+ (swb11-address-offset right) right-length)
    (swb11-address-offset left))
   (<=
    (+ (swb11-address-offset left) left-length)
    (swb11-address-offset right))))

;; Exact unfolding of Memory.framed for t_5.

(defun-sk swb11-framed-p ()
  (forall (address)
    (implies
     (swb11-address-p address)
     (<=
      (swb11-region
       (swb11-address-base (swb11-t5 address)))
      0))))

;; Exact havoc_access values for a_24 = havoc t_2 t_3 and
;; a_22 = havoc t_1 t_3.

(defun swb11-havoc12-value
    (protected-start protected-length query)
  (if
      (swb11-separated-p
       query 1 protected-start protected-length)
      (swb11-t3 query)
    (swb11-t2 query)))

(defun swb11-havoc21-value
    (protected-start protected-length query)
  (if
      (swb11-separated-p
       query 1 protected-start protected-length)
      (swb11-t3 query)
    (swb11-t1 query)))

;; Exact function extensional equality a_24 = t_4 over every source address.

(defun-sk swb11-havoc12-equals-t4-p (protected-start)
  (forall (address)
    (implies
     (swb11-address-p address)
     (equal
      (swb11-havoc12-value
       protected-start
       (swb11-l-size)
       address)
      (swb11-t4 address)))))

;; Exact unfoldings of p_idle_core for t_4 and for the havoced memory a_24.

(defun-sk swb11-idle-core-t4-p (cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb11-t4
         (swb11-shift
          (swb11-t5
           (swb11-shift
            (swb11-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb11-l-size))
        (not
         (equal
          (swb11-l-idle-cpu index)
          0))))))))

(defun-sk swb11-idle-core-havoc12-p
    (protected-start cpu)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb11-havoc12-value
         protected-start
         (swb11-l-size)
         (swb11-shift
          (swb11-t5
           (swb11-shift
            (swb11-l-cpu-smt-mask cpu)
            0))
          index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb11-l-size))
        (not
         (equal
          (swb11-l-idle-cpu index)
          0))))))))

;; The existential paired-selection condition shared by three hypotheses.

(defun-sk swb11-selected-tail-exists-p
    (protected-start a10 a6 x4)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swb11-havoc12-value
        protected-start
        (swb11-l-size)
        (swb11-shift a10 index))
       0))
     (not
      (equal
       (swb11-havoc12-value
        protected-start
        (swb11-l-size)
        (swb11-shift a6 index))
       0))
     (< index (swb11-l-size))
     (<= x4 index))))

;; When i_1 is -1, every selected a_23 position maps to a selected a_19
;; position.

(defun-sk swb11-a18-to-a10-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb11-havoc12-value
         protected-start
         (swb11-l-size)
         (swb11-shift a18 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb11-l-size))
        (not
         (equal
          (swb11-havoc12-value
           protected-start
           (swb11-l-size)
           (swb11-shift a10 index))
          0))))))))

;; At every position from x_5 through l_size, at least one mask is zero.

(defun-sk swb11-tail-zero-p
    (protected-start a10 a6 x4)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index (swb11-l-size))
      (implies
       (<= x4 index)
       (or
        (equal
         (swb11-havoc12-value
          protected-start
          (swb11-l-size)
          (swb11-shift a10 index))
         0)
        (equal
         (swb11-havoc12-value
          protected-start
          (swb11-l-size)
          (swb11-shift a6 index))
         0)))))))

;; Every position selected by both a_7 and a_23 below a bound has idle value
;; zero.

(defun-sk swb11-selected-prefix-idle-zero-p
    (protected-start a6 a18 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb11-havoc12-value
         protected-start
         (swb11-l-size)
         (swb11-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb11-havoc12-value
          protected-start
          (swb11-l-size)
          (swb11-shift a18 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index bound)
         (implies
          (< index (swb11-l-size))
          (equal
           (swb11-l-idle-cpu index)
           0)))))))))

;; The paired-zero condition below i_3.

(defun-sk swb11-prefix-zero-p
    (protected-start a10 a6 x4 i6)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index i6)
      (implies
       (<= x4 index)
       (or
        (equal
         (swb11-havoc12-value
          protected-start
          (swb11-l-size)
          (swb11-shift a10 index))
         0)
        (equal
         (swb11-havoc12-value
          protected-start
          (swb11-l-size)
          (swb11-shift a6 index))
         0)))))))

;; Every position selected by both masks in [i_1, i_4) is not an idle core.

(defun-sk swb11-selected-range-not-idle-core-p
    (protected-start a6 a18 i1 i7)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb11-havoc12-value
         protected-start
         (swb11-l-size)
         (swb11-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb11-havoc12-value
          protected-start
          (swb11-l-size)
          (swb11-shift a18 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (<= i1 index)
         (implies
          (< index i7)
          (implies
           (< index (swb11-l-size))
           (not
            (swb11-idle-core-havoc12-p
             protected-start index)))))))))))

;; A selected a_23 position has either a selected a_19 position or is not an
;; idle core.

(defun-sk swb11-a18-to-a10-or-not-idle-core-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb11-havoc12-value
         protected-start
         (swb11-l-size)
         (swb11-shift a18 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb11-l-size))
        (or
         (not
          (equal
           (swb11-havoc12-value
            protected-start
            (swb11-l-size)
            (swb11-shift a10 index))
           0))
         (not
          (swb11-idle-core-havoc12-p
           protected-start index)))))))))

;; Separation of a_21 from every pointed-to CPU mask in the source array.

(defun-sk swb11-a20-separated-p (a20 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb11-l-size))
       (swb11-separated-p
        a20
        (swb11-l-size)
        (swb11-shift
         (swb11-t5
          (swb11-shift
           (swb11-shift a index)
           0))
         0)
        (swb11-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb11-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((a28 (swb11-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb11-l-size))
         (and
          (swb11-valid-rd-p a28 1)
          (swb11-valid-rw-p
           (swb11-shift
            (swb11-t5
             (swb11-shift a28 0))
            0)
           (swb11-l-size)))))))))

;; The two a_22 mask views agree at every valid array index.

(defun-sk swb11-havoc21-agreement-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb11-l-size))
       (iff
        (not
         (equal
          (swb11-havoc21-value
           protected-start
           (swb11-l-size)
           (swb11-shift a18 index))
          0))
        (not
         (equal
          (swb11-havoc21-value
           protected-start
           (swb11-l-size)
           (swb11-shift a10 index))
          0))))))))

;; Every selected a_19 position in a_24 is selected in a_23.

(defun-sk swb11-a10-to-a18-p
    (protected-start a10 a18)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb11-havoc12-value
         protected-start
         (swb11-l-size)
         (swb11-shift a10 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb11-l-size))
        (not
         (equal
          (swb11-havoc12-value
           protected-start
           (swb11-l-size)
           (swb11-shift a18 index))
          0))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb11-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb11-l-size))
       (swb11-separated-p
        mask
        (swb11-l-size)
        (swb11-shift
         (swb11-t5
          (swb11-shift
           (swb11-shift a index)
           0))
         0)
        (swb11-l-size)))))))

(defun-sk swb11-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb11-address-p address)
     (let*
         ((a29 (swb11-l-sched-group-cpus address))
          (a30
           (swb11-shift
            (swb11-t5
             (swb11-shift a29 0))
            0)))
       (and
        (swb11-valid-rd-p a29 1)
        (swb11-valid-rd-p a30 (swb11-l-size))
        (swb11-separated-from-array-masks-p a30 a))))))

(defun-sk swb11-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb11-address-p address)
     (let*
         ((a29 (swb11-l-sched-group-mask address))
          (a30
           (swb11-shift
            (swb11-t5
             (swb11-shift a29 0))
            0)))
       (and
        (swb11-valid-rd-p a29 1)
        (swb11-valid-rd-p a30 (swb11-l-size))
        (swb11-separated-from-array-masks-p a30 a))))))

(defun-sk swb11-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb11-address-p address)
     (let*
         ((a29 (swb11-l-group-balance-mask address))
          (a30
           (swb11-shift
            (swb11-t5
             (swb11-shift a29 0))
            0)))
       (and
        (swb11-valid-rd-p a29 1)
        (swb11-valid-rd-p a30 (swb11-l-size))
        (swb11-separated-from-array-masks-p a30 a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb11-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((a28 (swb11-l-cpu-smt-mask index))
          (a29
           (swb11-shift
            (swb11-t5
             (swb11-shift a28 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb11-l-size))
         (and
          (swb11-valid-rd-p a28 1)
          (swb11-valid-rd-p a29 (swb11-l-size))
          (swb11-separated-from-array-masks-p a29 a))))))))

(defun swb11-goal-body
    (i3 a1 a i a2 i1 i4 i2 p)
  (implies
   (and
    (swb11-function-types-p)
    (swb11-scheduler-schema-types-p)
    (swb11-zero-mask-memory-instance-p)
    (swb11-q-mask-refl-p)
    (swb11-q-mask-symm-p)
    (swb11-q-mask-trans-p)
    (integerp (swb11-l-size))
    (< 0 (swb11-l-size))
    (<= (swb11-l-size) 2147483647)
    (swb11-address-p a1)
    (swb11-address-p a)
    (swb11-address-p a2)
    (integerp i3)
    (integerp i)
    (integerp i1)
    (integerp i4)
    (integerp i2)
    (booleanp p))
   (let*
       ((x (swb11-l-idle-cpu i3))
        (a3 (swb11-shift a1 3))
        (x1 (swb11-t3 a3))
        (a4 (swb11-shift a1 4))
        (a5 (swb11-t5 a4))
        (a6 (swb11-shift a5 0))
        (a7 (swb11-t5 a6))
        (a8 (swb11-shift a1 1))
        (x2 (swb11-t3 a8))
        (x3 (swb11-t3 (swb11-shift a7 x2)))
        (a9 (swb11-shift a1 0))
        (a10 (swb11-shift a i))
        (a11 (swb11-t5 a9))
        (a12 (swb11-shift a11 1))
        (a13 (swb11-shift a2 0))
        (a14 (swb11-shift (swb11-t5 a13) 1))
        (x4 (swb11-t4 a14))
        (a15 (swb11-shift a10 0))
        (a16 (swb11-shift a11 0))
        (a17 (swb11-t5 a16))
        (a18 (swb11-l-group-balance-mask a17))
        (a19 (swb11-t5 a15))
        (a20 (swb11-shift a19 0))
        (a21 (swb11-shift a7 0))
        (a23
         (swb11-t5
          (swb11-shift a18 0)))
        (a25
         (swb11-havoc12-value
          a20
          (swb11-l-size)
          (swb11-shift a19 i3)))
        (a26
         (swb11-havoc12-value
          a20
          (swb11-l-size)
          (swb11-shift a7 i1)))
        (a27
         (swb11-havoc12-value
          a20
          (swb11-l-size)
          (swb11-shift a7 i3)))
        (a28
         (swb11-havoc12-value
          a20
          (swb11-l-size)
          (swb11-shift a23 i1)))
        (a29
         (swb11-havoc12-value
          a20
          (swb11-l-size)
          a12))
        (a30 (swb11-shift a23 0))
        (x5 (swb11-to-uint32 i4)))
     (implies
      (and
       (iff
        (not (equal x 0))
        (not (equal i2 0)))
       (not (equal x1 2))
       (not (equal x3 0))
       (<= 0 i)
       (< i (swb11-l-size))
       (<= 0 i3)
       (< i3 (swb11-l-size))
       (<= 0 i4)
       (<= i4 (swb11-l-size))
       (< (swb11-to-uint32 i3) (swb11-l-size))
       (<= 0 x2)
       (< x2 (swb11-l-size))
       (<= (swb11-region (swb11-address-base a)) 0)
       (<= (swb11-region (swb11-address-base a1)) 0)
       (swb11-framed-p)
       (swb11-linked-p)
       (swb11-is-uint8-p i2)
       (swb11-is-uint32-p i)
       (swb11-is-sint32-p i1)
       (swb11-is-sint32-p i3)
       (swb11-is-sint32-p i4)
       (swb11-valid-rd-p a1 5)
       (swb11-is-uint32-p x1)
       (swb11-is-sint32-p (+ 1 i3))
       (swb11-is-sint32-p x2)
       (swb11-valid-rd-p a4 1)
       (swb11-valid-rd-p a8 1)
       (swb11-valid-rd-p a3 1)
       (swb11-valid-rd-p a9 1)
       (swb11-valid-rd-p a10 1)
       (swb11-valid-rd-p a5 1)
       (swb11-valid-rd-p
        (swb11-t5 (swb11-shift a1 2))
        2)
       (swb11-valid-rd-p a11 2)
       (swb11-is-sint32-p (swb11-t3 a12))
       (swb11-is-sint32-p x4)
       (swb11-valid-rd-p a15 1)
       (swb11-valid-rd-p a6 1)
       (swb11-valid-rd-p a16 1)
       (swb11-valid-rd-p a17 1)
       (swb11-valid-rd-p a18 1)
       (swb11-is-uint8-p x3)
       (swb11-valid-rd-p a20 (swb11-l-size))
       (swb11-valid-rd-p a21 (swb11-l-size))
       (swb11-valid-rw-p a20 (swb11-l-size))
       (swb11-is-uint8-p
        (swb11-havoc21-value
         a20
         (swb11-l-size)
         (swb11-shift a7 -1)))
       (swb11-is-uint8-p
        (swb11-havoc21-value
         a20
         (swb11-l-size)
         (swb11-shift a23 -1)))
       (swb11-is-uint8-p a25)
       (swb11-is-uint8-p a26)
       (swb11-is-uint8-p a27)
       (swb11-is-uint8-p a28)
       (swb11-is-sint32-p
        (swb11-havoc21-value
         a20
         (swb11-l-size)
         a12))
       (swb11-is-sint32-p a29)
       (swb11-valid-rd-p a30 (swb11-l-size))
       (swb11-separated-p
        a20
        (swb11-l-size)
        a30
        (swb11-l-size))
       (if
           (equal i2 0)
           (<= i3 2147483646)
         (and
          (equal p nil)
          (equal a2 a1)
          (not (equal x 0))
          (equal
           (swb11-land 7 x4)
           0)
          (swb11-havoc12-equals-t4-p a20)
          (<= i3 2147483646)
          (not (swb11-idle-core-t4-p i3))
          (swb11-valid-rd-p a13 1)
          (swb11-valid-rd-p a14 1)))
       (implies
        (not
         (equal
          (swb11-land 7 a29)
          0))
        (equal i1 -1))
       (implies
        (not (equal i1 -1))
        (and
         (not (equal (swb11-l-idle-cpu i1) 0))
         (not (equal a26 0))
         (not (equal a28 0))
         (<= 0 i1)
         (< i1 (swb11-l-size))))
       (implies
        (equal i1 -1)
        (swb11-a18-to-a10-p a20 a23 a19))
       (implies
        (swb11-selected-tail-exists-p
         a20 a19 a7 x5)
        (<= x5 i3))
       (implies
        (swb11-selected-tail-exists-p
         a20 a19 a7 x5)
        (and
         (not (equal a25 0))
         (not (equal a27 0))))
       (implies
        (swb11-tail-zero-p a20 a19 a7 x5)
        (equal (swb11-l-size) i3))
       (implies
        (not (equal i1 -1))
        (swb11-selected-prefix-idle-zero-p
         a20 a7 a23 i1))
       (implies
        (equal i1 -1)
        (swb11-selected-prefix-idle-zero-p
         a20 a7 a23 i4))
       (implies
        (swb11-selected-tail-exists-p
         a20 a19 a7 x5)
        (swb11-prefix-zero-p
         a20 a19 a7 x5 i3))
       (implies
        (not (equal i1 -1))
        (swb11-selected-range-not-idle-core-p
         a20 a7 a23 i1 i4))
       (implies
        (not (equal i1 -1))
        (swb11-a18-to-a10-or-not-idle-core-p
         a20 a23 a19))
       (or (equal i2 0) (equal i2 1))
       (swb11-a20-separated-p a21 a)
       (swb11-array-layout-p a)
       (swb11-havoc21-agreement-p a20 a23 a19)
       (swb11-a10-to-a18-p a20 a19 a23)
       (swb11-sched-group-cpus-layout-p a)
       (swb11-sched-group-mask-layout-p a)
       (swb11-group-balance-mask-layout-p a)
       (swb11-cpu-smt-layout-p a))
      (<= -1 i3)))))

(defun-sk
    ntp4vc-should-we-balance-loop-inv-preserved-goal11-statement ()
  (forall
   (i3 a1 a i a2 i1 i4 i2 p)
   (swb11-goal-body
    i3 a1 a i a2 i1 i4 i2 p)))

(value-triple :itpeval-statement-checked)

:q
