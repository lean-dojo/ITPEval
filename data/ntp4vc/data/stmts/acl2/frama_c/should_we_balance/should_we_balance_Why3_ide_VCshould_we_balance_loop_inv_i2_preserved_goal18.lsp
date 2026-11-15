;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_i2_preserved_goal18:
;; preservation of the idle-CPU loop invariant under integer bounds, memory
;; validity, framing, separation, havoc-memory agreement, and quantified
;; scheduling and CPU-mask layout hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb18-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb18-address-base (address)
  (car address))

(defun swb18-address-offset (address)
  (cdr address))

(defun swb18-shift (address amount)
  (cons
   (swb18-address-base address)
   (+ (swb18-address-offset address) amount)))

;; Conservative interfaces for the arbitrary source memory functions t_1,
;; t_2, t_3, t_4, allocation map t, and the fixed source symbols.

(defstub swb18-t1 (address) t)
(defstub swb18-t2 (address) t)
(defstub swb18-t3 (address) t)
(defstub swb18-t4 (address) t)
(defstub swb18-allocation (index) t)
(defstub swb18-region (base) t)
(defstub swb18-linked-op () t)
(defstub swb18-l-size () t)
(defstub swb18-mask-memory-apply (memory-symbol address) t)
(defstub swb18-mask-pointer-apply (pointer-symbol address) t)
(defstub swb18-l-idle-cpu (index) t)
(defstub swb18-l-sched-group-cpus (address) t)
(defstub swb18-l-sched-group-mask (address) t)
(defstub swb18-l-group-balance-mask (address) t)
(defstub swb18-l-cpu-smt-mask (index) t)

(defun swb18-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb18-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb18-address-p address)
      (and
       (integerp
        (swb18-mask-memory-apply
         memory-symbol address))
       (swb18-address-p
        (swb18-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb18-is-uint8-p
        (swb18-l-idle-cpu index))
       (swb18-address-p
        (swb18-l-cpu-smt-mask index)))))))

(defun-sk swb18-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb18-address-p address)
     (equal
      (swb18-mask-memory-apply
       'swb18-zero-memory address)
      0))))

(defun-sk swb18-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb18-l-size)))
     (not
      (equal
       (swb18-mask-memory-apply
        memory-symbol
        (swb18-shift
         (swb18-mask-pointer-apply
          pointer-symbol
          (swb18-shift
           (swb18-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb18-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb18-mask-memory-apply
         memory-symbol
         (swb18-shift
          (swb18-mask-pointer-apply
           pointer-symbol
           (swb18-shift
            (swb18-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb18-l-size))
      (<= 0 j)
      (< j (swb18-l-size)))
     (not
      (equal
       (swb18-mask-memory-apply
        memory-symbol
        (swb18-shift
         (swb18-mask-pointer-apply
          pointer-symbol
          (swb18-shift
           (swb18-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb18-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb18-mask-memory-apply
         memory-symbol
         (swb18-shift
          (swb18-mask-pointer-apply
           pointer-symbol
           (swb18-shift
            (swb18-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb18-mask-memory-apply
         memory-symbol
         (swb18-shift
          (swb18-mask-pointer-apply
           pointer-symbol
           (swb18-shift
            (swb18-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb18-l-size))
      (<= 0 j)
      (< j (swb18-l-size))
      (<= 0 k)
      (< k (swb18-l-size)))
     (not
      (equal
       (swb18-mask-memory-apply
        memory-symbol
        (swb18-shift
         (swb18-mask-pointer-apply
          pointer-symbol
          (swb18-shift
           (swb18-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb18-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb18-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These clauses preserve the source function types over the full unbounded
;; integer and address domains, together with the imported idle-CPU range.

(defun-sk swb18-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb18-address-p address)
      (and
       (integerp (swb18-t1 address))
       (integerp (swb18-t2 address))
       (integerp (swb18-t3 address))
       (swb18-address-p (swb18-t4 address))
       (swb18-address-p
        (swb18-l-sched-group-cpus address))
       (swb18-address-p
        (swb18-l-sched-group-mask address))
       (swb18-address-p
        (swb18-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb18-allocation index))
       (swb18-is-uint8-p (swb18-l-idle-cpu index))
       (swb18-address-p (swb18-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb18-region base))))))

(defun swb18-linked-p ()
  (if (swb18-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun swb18-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb18-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb18-address-base address))
    (<= 0 (swb18-address-offset address))
    (<=
     (+ (swb18-address-offset address) length)
     (swb18-allocation (swb18-address-base address))))))

(defun swb18-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb18-address-base address)))
    (<= 0 (swb18-address-offset address))
    (<=
     (+ (swb18-address-offset address) length)
     (swb18-allocation (swb18-address-base address))))))

(defun swb18-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb18-address-base left)
     (swb18-address-base right)))
   (<=
    (+ (swb18-address-offset right) right-length)
    (swb18-address-offset left))
   (<=
    (+ (swb18-address-offset left) left-length)
    (swb18-address-offset right))))

;; Exact unfolding of Memory.framed for t_4.

(defun-sk swb18-framed-p ()
  (forall (address)
    (implies
     (swb18-address-p address)
     (<=
      (swb18-region
       (swb18-address-base (swb18-t4 address)))
      0))))

;; Exact havoc_access values for a_12 = havoc t_2 t_3 and
;; a_21 = havoc t_1 t_3.

(defun swb18-havoc12-value
    (protected-start protected-length query)
  (if
      (swb18-separated-p
       query 1 protected-start protected-length)
      (swb18-t3 query)
    (swb18-t2 query)))

(defun swb18-havoc21-value
    (protected-start protected-length query)
  (if
      (swb18-separated-p
       query 1 protected-start protected-length)
      (swb18-t3 query)
    (swb18-t1 query)))

;; The existential paired-selection condition shared by three hypotheses.

(defun-sk swb18-selected-tail-exists-p
    (protected-start a10 a6 x3)
  (exists (index)
    (and
     (integerp index)
     (not
      (equal
       (swb18-havoc12-value
        protected-start
        (swb18-l-size)
        (swb18-shift a10 index))
       0))
     (not
      (equal
       (swb18-havoc12-value
        protected-start
        (swb18-l-size)
        (swb18-shift a6 index))
       0))
     (< index (swb18-l-size))
     (<= x3 index))))

;; At every position from x_3 through l_size, at least one mask is zero.

(defun-sk swb18-tail-zero-p
    (protected-start a10 a6 x3)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index (swb18-l-size))
      (implies
       (<= x3 index)
       (or
        (equal
         (swb18-havoc12-value
          protected-start
          (swb18-l-size)
          (swb18-shift a10 index))
         0)
        (equal
         (swb18-havoc12-value
          protected-start
          (swb18-l-size)
          (swb18-shift a6 index))
         0)))))))

;; The same paired-zero condition below i_2.

(defun-sk swb18-prefix-zero-p
    (protected-start a10 a6 x3 i2)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (< index i2)
      (implies
       (<= x3 index)
       (or
        (equal
         (swb18-havoc12-value
          protected-start
          (swb18-l-size)
          (swb18-shift a10 index))
         0)
        (equal
         (swb18-havoc12-value
          protected-start
          (swb18-l-size)
          (swb18-shift a6 index))
         0)))))))

;; Separation of a_20 from every pointed-to CPU mask in the source array.

(defun-sk swb18-a20-separated-p (a20 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb18-l-size))
       (swb18-separated-p
        a20
        (swb18-l-size)
        (swb18-shift
         (swb18-t4
          (swb18-shift
           (swb18-shift a index)
           0))
         0)
        (swb18-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb18-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((element (swb18-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb18-l-size))
         (and
          (swb18-valid-rd-p element 1)
          (swb18-valid-rw-p
           (swb18-shift
            (swb18-t4
             (swb18-shift element 0))
            0)
           (swb18-l-size)))))))))

;; The two a_21 mask views agree at every valid array index.

(defun-sk swb18-havoc21-agreement-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb18-l-size))
       (iff
        (not
         (equal
          (swb18-havoc21-value
           protected-start
           (swb18-l-size)
           (swb18-shift a18 index))
          0))
        (not
         (equal
          (swb18-havoc21-value
           protected-start
           (swb18-l-size)
           (swb18-shift a10 index))
          0))))))))

;; Every selected a_18 position in a_12 is selected in a_10.

(defun-sk swb18-a18-to-a10-p
    (protected-start a18 a10)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb18-havoc12-value
         protected-start
         (swb18-l-size)
         (swb18-shift a18 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb18-l-size))
        (not
         (equal
          (swb18-havoc12-value
           protected-start
           (swb18-l-size)
           (swb18-shift a10 index))
          0))))))))

;; Every selected a_10 position in a_12 is selected in a_18.

(defun-sk swb18-a10-to-a18-p
    (protected-start a10 a18)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb18-havoc12-value
         protected-start
         (swb18-l-size)
         (swb18-shift a10 index))
        0))
      (implies
       (<= 0 index)
       (implies
        (< index (swb18-l-size))
        (not
         (equal
          (swb18-havoc12-value
           protected-start
           (swb18-l-size)
           (swb18-shift a18 index))
          0))))))))

;; Every position selected by both a_6 and a_18 below i_3 has idle value zero.

(defun-sk swb18-selected-prefix-idle-zero-p
    (protected-start a6 a18 i3)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (equal
        (swb18-havoc12-value
         protected-start
         (swb18-l-size)
         (swb18-shift a6 index))
        0))
      (implies
       (not
        (equal
         (swb18-havoc12-value
          protected-start
          (swb18-l-size)
          (swb18-shift a18 index))
         0))
       (implies
        (<= 0 index)
        (implies
         (< index i3)
         (implies
          (< index (swb18-l-size))
          (equal
           (swb18-l-idle-cpu index)
           0)))))))))

;; The separation clause shared by the group-mask and CPU-mask hypotheses.

(defun-sk swb18-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb18-l-size))
       (swb18-separated-p
        mask
        (swb18-l-size)
        (swb18-shift
         (swb18-t4
          (swb18-shift
           (swb18-shift a index)
           0))
         0)
        (swb18-l-size)))))))

;; The three universally quantified group-layout hypotheses.

(defun-sk swb18-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb18-address-p address)
     (let*
         ((field (swb18-l-sched-group-cpus address))
          (mask
           (swb18-shift
            (swb18-t4
             (swb18-shift field 0))
            0)))
       (and
        (swb18-valid-rd-p field 1)
        (swb18-valid-rd-p mask (swb18-l-size))
        (swb18-separated-from-array-masks-p mask a))))))

(defun-sk swb18-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb18-address-p address)
     (let*
         ((field (swb18-l-sched-group-mask address))
          (mask
           (swb18-shift
            (swb18-t4
             (swb18-shift field 0))
            0)))
       (and
        (swb18-valid-rd-p field 1)
        (swb18-valid-rd-p mask (swb18-l-size))
        (swb18-separated-from-array-masks-p mask a))))))

(defun-sk swb18-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb18-address-p address)
     (let*
         ((field (swb18-l-group-balance-mask address))
          (mask
           (swb18-shift
            (swb18-t4
             (swb18-shift field 0))
            0)))
       (and
        (swb18-valid-rd-p field 1)
        (swb18-valid-rd-p mask (swb18-l-size))
        (swb18-separated-from-array-masks-p mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb18-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((field (swb18-l-cpu-smt-mask index))
          (mask
           (swb18-shift
            (swb18-t4
             (swb18-shift field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb18-l-size))
         (and
          (swb18-valid-rd-p field 1)
          (swb18-valid-rd-p mask (swb18-l-size))
          (swb18-separated-from-array-masks-p mask a))))))))

(defun swb18-goal-body (a1 a i i2 i3 i1)
  (implies
   (and
    (swb18-function-types-p)
    (swb18-scheduler-schema-types-p)
    (swb18-zero-mask-memory-instance-p)
    (swb18-q-mask-refl-p)
    (swb18-q-mask-symm-p)
    (swb18-q-mask-trans-p)
    (integerp (swb18-l-size))
    (< 0 (swb18-l-size))
    (<= (swb18-l-size) 2147483647)
    (swb18-address-p a1)
    (swb18-address-p a)
    (integerp i)
    (integerp i2)
    (integerp i3)
    (integerp i1))
   (let*
       ((a2 (swb18-shift a1 3))
        (x (swb18-t3 a2))
        (a3 (swb18-shift a1 4))
        (a4 (swb18-t4 a3))
        (a5 (swb18-shift a4 0))
        (a6 (swb18-t4 a5))
        (a7 (swb18-shift a1 1))
        (x1 (swb18-t3 a7))
        (x2 (swb18-t3 (swb18-shift a6 x1)))
        (a8 (swb18-shift a i))
        (a9 (swb18-shift a8 0))
        (a10 (swb18-t4 a9))
        (a11 (swb18-shift a10 0))
        (a13 (swb18-shift a1 0))
        (a14 (swb18-t4 a13))
        (a15 (swb18-shift a14 0))
        (a16 (swb18-t4 a15))
        (a17 (swb18-l-group-balance-mask a16))
        (a18
         (swb18-t4
          (swb18-shift a17 0)))
        (a19 (swb18-shift a14 1))
        (a20 (swb18-shift a6 0))
        (a22 (swb18-shift a6 -1))
        (a23 (swb18-shift a18 -1))
        (a24
         (swb18-havoc12-value
          a11
          (swb18-l-size)
          (swb18-shift a10 i2)))
        (a25
         (swb18-havoc12-value
          a11
          (swb18-l-size)
          (swb18-shift a6 i2)))
        (a26 (swb18-shift a18 0))
        (x3 (swb18-to-uint32 i3)))
     (implies
      (and
       (equal (swb18-l-idle-cpu i2) 0)
       (not (equal x 2))
       (not (equal x2 0))
       (not
        (equal
         (swb18-havoc12-value
          a11
          (swb18-l-size)
          (swb18-shift a6 i1))
         0))
       (not
        (equal
         (swb18-havoc12-value
          a11
          (swb18-l-size)
          (swb18-shift a18 i1))
         0))
       (<= 0 i)
       (< i (swb18-l-size))
       (<= 0 i1)
       (< i1 (swb18-l-size))
       (<= 0 i2)
       (<= i1 i2)
       (< i2 (swb18-l-size))
       (<= 0 i3)
       (<= i3 (swb18-l-size))
       (< (swb18-to-uint32 i2) (swb18-l-size))
       (<= 0 x1)
       (< x1 (swb18-l-size))
       (<= (swb18-region (swb18-address-base a)) 0)
       (<= (swb18-region (swb18-address-base a1)) 0)
       (<= i2 2147483646)
       (swb18-framed-p)
       (swb18-linked-p)
       (swb18-is-uint32-p i)
       (swb18-is-sint32-p i2)
       (swb18-is-sint32-p i3)
       (swb18-valid-rd-p a1 5)
       (swb18-is-uint32-p x)
       (swb18-is-sint32-p (+ 1 i2))
       (swb18-is-sint32-p x1)
       (swb18-valid-rd-p a3 1)
       (swb18-valid-rd-p a7 1)
       (swb18-valid-rd-p a2 1)
       (swb18-valid-rd-p a13 1)
       (swb18-valid-rd-p a8 1)
       (swb18-valid-rd-p a4 1)
       (swb18-valid-rd-p
        (swb18-t4 (swb18-shift a1 2))
        2)
       (swb18-valid-rd-p a14 2)
       (swb18-is-sint32-p (swb18-t3 a19))
       (swb18-valid-rd-p a9 1)
       (swb18-valid-rd-p a5 1)
       (swb18-valid-rd-p a15 1)
       (swb18-valid-rd-p a16 1)
       (swb18-valid-rd-p a17 1)
       (swb18-is-uint8-p x2)
       (swb18-valid-rd-p a11 (swb18-l-size))
       (swb18-valid-rd-p a20 (swb18-l-size))
       (swb18-valid-rw-p a11 (swb18-l-size))
       (swb18-is-uint8-p
        (swb18-havoc21-value
         a11
         (swb18-l-size)
         a22))
       (swb18-is-uint8-p
        (swb18-havoc21-value
         a11
         (swb18-l-size)
         a23))
       (swb18-is-uint8-p a24)
       (swb18-is-uint8-p
        (swb18-havoc12-value
         a11
         (swb18-l-size)
         a22))
       (swb18-is-uint8-p a25)
       (swb18-is-uint8-p
        (swb18-havoc12-value
         a11
         (swb18-l-size)
         a23))
       (swb18-is-sint32-p
        (swb18-havoc21-value
         a11
         (swb18-l-size)
         a19))
       (swb18-is-sint32-p
        (swb18-havoc12-value
         a11
         (swb18-l-size)
         a19))
       (swb18-valid-rd-p a26 (swb18-l-size))
       (swb18-separated-p
        a11
        (swb18-l-size)
        a26
        (swb18-l-size))
       (implies
        (swb18-selected-tail-exists-p
         a11 a10 a6 x3)
        (<= x3 i2))
       (implies
        (swb18-selected-tail-exists-p
         a11 a10 a6 x3)
        (and
         (not (equal a24 0))
         (not (equal a25 0))))
       (implies
        (swb18-tail-zero-p a11 a10 a6 x3)
        (equal (swb18-l-size) i2))
       (implies
        (swb18-selected-tail-exists-p
         a11 a10 a6 x3)
        (swb18-prefix-zero-p
         a11 a10 a6 x3 i2))
       (swb18-a20-separated-p a20 a)
       (swb18-array-layout-p a)
       (swb18-havoc21-agreement-p a11 a18 a10)
       (swb18-a18-to-a10-p a11 a18 a10)
       (swb18-a10-to-a18-p a11 a10 a18)
       (swb18-selected-prefix-idle-zero-p
        a11 a6 a18 i3)
       (swb18-sched-group-cpus-layout-p a)
       (swb18-sched-group-mask-layout-p a)
       (swb18-group-balance-mask-layout-p a)
       (swb18-cpu-smt-layout-p a))
      (equal (swb18-l-idle-cpu i1) 0)))))

(defun-sk
    ntp4vc-should-we-balance-loop-inv-i2-preserved-goal18-statement ()
  (forall
   (a1 a i i2 i3 i1)
   (swb18-goal-body a1 a i i2 i3 i1)))

(value-triple :itpeval-statement-checked)

:q
