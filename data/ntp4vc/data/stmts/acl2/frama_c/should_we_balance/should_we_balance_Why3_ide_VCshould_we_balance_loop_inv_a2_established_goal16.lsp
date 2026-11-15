;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_a2_established_goal16:
;; establishment of a CPU-mask loop invariant from havoc-memory agreement,
;; integer bounds, memory validity, separation, framing, and quantified
;; scheduling-layout hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun swb16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun swb16-address-base (address)
  (car address))

(defun swb16-address-offset (address)
  (cdr address))

(defun swb16-shift (address amount)
  (cons
   (swb16-address-base address)
   (+ (swb16-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source integer
;; memories t_1 and t_2, pointer memory t_3, allocation map t, and fixed
;; source symbols.

(defstub swb16-t1 (address) t)
(defstub swb16-t2 (address) t)
(defstub swb16-t3 (address) t)
(defstub swb16-allocation (index) t)
(defstub swb16-region (base) t)
(defstub swb16-linked-op () t)
(defstub swb16-l-size () t)
(defstub swb16-l-idle-cpu (index) t)
(defstub swb16-mask-memory-apply (memory-symbol address) t)
(defstub swb16-mask-pointer-apply (pointer-symbol address) t)
(defstub swb16-l-sched-group-cpus (address) t)
(defstub swb16-l-sched-group-mask (address) t)
(defstub swb16-l-group-balance-mask (address) t)
(defstub swb16-l-cpu-smt-mask (index) t)

(defun swb16-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))
;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk swb16-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (swb16-address-p address)
      (and
       (integerp
        (swb16-mask-memory-apply
         memory-symbol address))
       (swb16-address-p
        (swb16-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (swb16-is-uint8-p
        (swb16-l-idle-cpu index))
       (swb16-address-p
        (swb16-l-cpu-smt-mask index)))))))

(defun-sk swb16-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (swb16-address-p address)
     (equal
      (swb16-mask-memory-apply
       'swb16-zero-memory address)
      0))))

(defun-sk swb16-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (swb16-l-size)))
     (not
      (equal
       (swb16-mask-memory-apply
        memory-symbol
        (swb16-shift
         (swb16-mask-pointer-apply
          pointer-symbol
          (swb16-shift
           (swb16-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk swb16-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (swb16-mask-memory-apply
         memory-symbol
         (swb16-shift
          (swb16-mask-pointer-apply
           pointer-symbol
           (swb16-shift
            (swb16-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (swb16-l-size))
      (<= 0 j)
      (< j (swb16-l-size)))
     (not
      (equal
       (swb16-mask-memory-apply
        memory-symbol
        (swb16-shift
         (swb16-mask-pointer-apply
          pointer-symbol
          (swb16-shift
           (swb16-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk swb16-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (swb16-mask-memory-apply
         memory-symbol
         (swb16-shift
          (swb16-mask-pointer-apply
           pointer-symbol
           (swb16-shift
            (swb16-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (swb16-mask-memory-apply
         memory-symbol
         (swb16-shift
          (swb16-mask-pointer-apply
           pointer-symbol
           (swb16-shift
            (swb16-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (swb16-l-size))
      (<= 0 j)
      (< j (swb16-l-size))
      (<= 0 k)
      (< k (swb16-l-size)))
     (not
      (equal
       (swb16-mask-memory-apply
        memory-symbol
        (swb16-shift
         (swb16-mask-pointer-apply
          pointer-symbol
          (swb16-shift
           (swb16-l-cpu-smt-mask i)
           0))
         k))
       0)))))


(defun swb16-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun swb16-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These clauses preserve the source function types over the full unbounded
;; integer and address domains.

(defun-sk swb16-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (swb16-address-p address)
      (and
       (integerp (swb16-t1 address))
       (integerp (swb16-t2 address))
       (swb16-address-p (swb16-t3 address))
       (swb16-address-p
        (swb16-l-sched-group-cpus address))
       (swb16-address-p
        (swb16-l-sched-group-mask address))
       (swb16-address-p
        (swb16-l-group-balance-mask address))))
     (implies
      (integerp index)
      (and
       (integerp (swb16-allocation index))
       (swb16-address-p (swb16-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (swb16-region base))))))

(defun swb16-linked-p ()
  (if (swb16-linked-op) t nil))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun swb16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (swb16-address-base address))
    (<= 0 (swb16-address-offset address))
    (<=
     (+ (swb16-address-offset address) length)
     (swb16-allocation (swb16-address-base address))))))

(defun swb16-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (swb16-address-base address)))
    (<= 0 (swb16-address-offset address))
    (<=
     (+ (swb16-address-offset address) length)
     (swb16-allocation (swb16-address-base address))))))

(defun swb16-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (swb16-address-base left)
     (swb16-address-base right)))
   (<=
    (+ (swb16-address-offset right) right-length)
    (swb16-address-offset left))
   (<=
    (+ (swb16-address-offset left) left-length)
    (swb16-address-offset right))))

;; Exact unfolding of Memory.framed for t_3.

(defun-sk swb16-framed-p ()
  (forall (address)
    (implies
     (swb16-address-p address)
     (<=
      (swb16-region
       (swb16-address-base (swb16-t3 address)))
      0))))

;; Exact value of havoc t_1 t_2 on the protected range.

(defun swb16-havoc-value
    (protected-start protected-length query)
  (if
      (swb16-separated-p
       query 1 protected-start protected-length)
      (swb16-t2 query)
    (swb16-t1 query)))

;; Separation from every pointed-to mask in the source array.

(defun-sk swb16-separated-from-array-masks-p (mask a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb16-l-size))
       (swb16-separated-p
        mask
        (swb16-l-size)
        (swb16-shift
         (swb16-t3
          (swb16-shift
           (swb16-shift a index)
           0))
         0)
        (swb16-l-size)))))))

;; The first quantified separation hypothesis for a_17.

(defun-sk swb16-a17-separated-p (a17 a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb16-l-size))
       (swb16-separated-p
        a17
        (swb16-l-size)
        (swb16-shift
         (swb16-t3
          (swb16-shift
           (swb16-shift a index)
           0))
         0)
        (swb16-l-size)))))))

;; Validity of every source array element and its pointed-to CPU mask.

(defun-sk swb16-array-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let ((element (swb16-shift a index)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb16-l-size))
         (and
          (swb16-valid-rd-p element 1)
          (swb16-valid-rw-p
           (swb16-shift
            (swb16-t3
             (swb16-shift element 0))
            0)
           (swb16-l-size)))))))))

;; Agreement of the two havoced views at every valid array index.

(defun-sk swb16-havoc-agreement-p (protected-start a16 a8)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index (swb16-l-size))
       (iff
        (not
         (equal
          (swb16-havoc-value
           protected-start
           (swb16-l-size)
           (swb16-shift a16 index))
          0))
        (not
         (equal
          (swb16-havoc-value
           protected-start
           (swb16-l-size)
           (swb16-shift a8 index))
          0))))))))

;; The three universally quantified group-layout hypotheses.

(defun-sk swb16-sched-group-cpus-layout-p (a)
  (forall (address)
    (implies
     (swb16-address-p address)
     (let*
         ((field (swb16-l-sched-group-cpus address))
          (mask
           (swb16-shift
            (swb16-t3
             (swb16-shift field 0))
            0)))
       (and
        (swb16-valid-rd-p field 1)
        (swb16-valid-rd-p mask (swb16-l-size))
        (swb16-separated-from-array-masks-p mask a))))))

(defun-sk swb16-sched-group-mask-layout-p (a)
  (forall (address)
    (implies
     (swb16-address-p address)
     (let*
         ((field (swb16-l-sched-group-mask address))
          (mask
           (swb16-shift
            (swb16-t3
             (swb16-shift field 0))
            0)))
       (and
        (swb16-valid-rd-p field 1)
        (swb16-valid-rd-p mask (swb16-l-size))
        (swb16-separated-from-array-masks-p mask a))))))

(defun-sk swb16-group-balance-mask-layout-p (a)
  (forall (address)
    (implies
     (swb16-address-p address)
     (let*
         ((field (swb16-l-group-balance-mask address))
          (mask
           (swb16-shift
            (swb16-t3
             (swb16-shift field 0))
            0)))
       (and
        (swb16-valid-rd-p field 1)
        (swb16-valid-rd-p mask (swb16-l-size))
        (swb16-separated-from-array-masks-p mask a))))))

;; The final quantified source hypothesis for every CPU SMT mask.

(defun-sk swb16-cpu-smt-layout-p (a)
  (forall (index)
    (implies
     (integerp index)
     (let*
         ((field (swb16-l-cpu-smt-mask index))
          (mask
           (swb16-shift
            (swb16-t3
             (swb16-shift field 0))
            0)))
       (implies
        (<= 0 index)
        (implies
         (< index (swb16-l-size))
         (and
          (swb16-valid-rd-p field 1)
          (swb16-valid-rd-p mask (swb16-l-size))
          (swb16-separated-from-array-masks-p mask a))))))))

(defun-sk
    ntp4vc-should-we-balance-loop-inv-a2-established-goal16-statement ()
  (forall
   (a1 a i i1)
   (implies
    (and
     (swb16-function-types-p)
     (swb16-scheduler-schema-types-p)
     (swb16-zero-mask-memory-instance-p)
     (swb16-q-mask-refl-p)
     (swb16-q-mask-symm-p)
     (swb16-q-mask-trans-p)
     (integerp (swb16-l-size))
     (< 0 (swb16-l-size))
     (<= (swb16-l-size) 2147483647)
     (swb16-address-p a1)
     (swb16-address-p a)
     (integerp i)
     (integerp i1))
    (let*
        ((a2 (swb16-shift a1 3))
         (x (swb16-t2 a2))
         (a3 (swb16-shift a1 4))
         (a4 (swb16-t3 a3))
         (a5
          (swb16-t3
           (swb16-shift a4 0)))
         (a6 (swb16-shift a1 1))
         (x1 (swb16-t2 a6))
         (x2
          (swb16-t2
           (swb16-shift a5 x1)))
         (a7 (swb16-shift a i))
         (a8
          (swb16-t3
           (swb16-shift a7 0)))
         (a9 (swb16-shift a8 0))
         (a11 (swb16-shift a1 0))
         (a12 (swb16-t3 a11))
         (a13 (swb16-shift a12 0))
         (a14 (swb16-t3 a13))
         (a15
          (swb16-l-group-balance-mask a14))
         (a16
          (swb16-t3
           (swb16-shift a15 0)))
         (a17 (swb16-shift a5 0))
         (a18 (swb16-shift a16 0)))
      (implies
       (and
        (not (equal x 2))
        (not (equal x2 0))
        (not
         (equal
          (swb16-havoc-value
           a9
           (swb16-l-size)
           (swb16-shift a16 i1))
          0))
        (<= 0 i)
        (< i (swb16-l-size))
        (<= 0 i1)
        (< i1 (swb16-l-size))
        (<= 0 x1)
        (< x1 (swb16-l-size))
        (<=
         (swb16-region (swb16-address-base a))
         0)
        (<=
         (swb16-region (swb16-address-base a1))
         0)
        (swb16-framed-p)
        (swb16-linked-p)
        (swb16-is-uint32-p i)
        (swb16-valid-rd-p a1 5)
        (swb16-is-uint32-p x)
        (swb16-is-sint32-p x1)
        (swb16-valid-rd-p a3 1)
        (swb16-valid-rd-p a6 1)
        (swb16-valid-rd-p a2 1)
        (swb16-valid-rd-p a11 1)
        (swb16-valid-rd-p a7 1)
        (swb16-valid-rd-p a4 1)
        (swb16-valid-rd-p
         (swb16-t3 (swb16-shift a1 2))
         2)
        (swb16-valid-rd-p a12 2)
        (swb16-is-sint32-p
         (swb16-t2 (swb16-shift a12 1)))
        (swb16-valid-rd-p a13 1)
        (swb16-valid-rd-p a14 1)
        (swb16-valid-rd-p a15 1)
        (swb16-is-uint8-p x2)
        (swb16-valid-rd-p
         a17
         (swb16-l-size))
        (swb16-valid-rw-p
         a9
         (swb16-l-size))
        (swb16-valid-rd-p
         a18
         (swb16-l-size))
        (swb16-separated-p
         a9
         (swb16-l-size)
         a18
         (swb16-l-size))
        (swb16-a17-separated-p a17 a)
        (swb16-array-layout-p a)
        (swb16-havoc-agreement-p a9 a16 a8)
        (swb16-sched-group-cpus-layout-p a)
        (swb16-sched-group-mask-layout-p a)
        (swb16-group-balance-mask-layout-p a)
        (swb16-cpu-smt-layout-p a))
       (not
        (equal
         (swb16-havoc-value
          a9
          (swb16-l-size)
          (swb16-shift a8 i1))
         0)))))))

(value-triple :itpeval-statement-checked)

:q
