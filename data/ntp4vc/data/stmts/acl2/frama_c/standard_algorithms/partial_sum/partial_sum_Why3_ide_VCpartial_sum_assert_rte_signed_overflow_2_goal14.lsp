;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sum/partial_sum_Why3_ide_VCpartial_sum_assert_rte_signed_overflow_2_goal14:
;; the signed 32-bit upper-overflow bound for the next partial-sum addition
;; under the stated index, memory, validity, separation, accumulation-bound,
;; unchanged-memory, and partial-sum hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ps14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ps14-address-base (address)
  (car address))

(defun ps14-address-offset (address)
  (cdr address))

(defun ps14-shift (address amount)
  (cons
   (ps14-address-base address)
   (+ (ps14-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memories t_2 and t_1, allocation map t, region function, and linked
;; predicate specialized to t.

(defstub ps14-t2 (address) t)
(defstub ps14-t1 (address) t)
(defstub ps14-allocation (index) t)
(defstub ps14-region (base) t)
(defstub ps14-linked-op () t)

(defun-sk ps14-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (ps14-address-p address)
      (and
       (integerp (ps14-t2 address))
       (integerp (ps14-t1 address))))
     (implies
      (integerp index)
      (integerp (ps14-allocation index)))
     (implies
      (integerp base)
      (integerp (ps14-region base))))))

(defun ps14-linked-p ()
  (if (ps14-linked-op) t nil))

(defun ps14-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ps14-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun ps14-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun ps14-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ps14-address-base address))
    (<= 0 (ps14-address-offset address))
    (<=
     (+ (ps14-address-offset address) length)
     (ps14-allocation (ps14-address-base address))))))

(defun ps14-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (ps14-address-base address)))
    (<= 0 (ps14-address-offset address))
    (<=
     (+ (ps14-address-offset address) length)
     (ps14-allocation (ps14-address-base address))))))

(defun ps14-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (ps14-address-base left)
     (ps14-address-base right)))
   (<=
    (+ (ps14-address-offset right) right-length)
    (ps14-address-offset left))
   (<=
    (+ (ps14-address-offset left) left-length)
    (ps14-address-offset right))))

;; Exact pointwise forms of Function.update t_2 a_2 x and
;; havoc t_1 (Function.update t_2 a_2 x) (shift a 1) (i - 1), using
;; Memory.havoc_access. Here x is t_2 (shift a_1 0).

(defun ps14-updated-t2-value (a a1 query)
  (if (equal query (ps14-shift a 0))
      (ps14-t2 (ps14-shift a1 0))
    (ps14-t2 query)))

(defun ps14-a4-value (a a1 i query)
  (if
      (ps14-separated-p
       query 1 (ps14-shift a 1) (- i 1))
      (ps14-updated-t2-value a a1 query)
    (ps14-t1 query)))

;; For the only initializer used by this VC, zero, the imported
;; Q_AccumulateEmpty and Q_AccumulateNext equations uniquely define these
;; exact partial sums for t_2 and a_4 over every integer length. The corrected
;; source authority omits the inconsistent global Q_TL_Accumulate range
;; axioms; signed-range information is scoped by p_accumulatebounds below.

(defun ps14-l-accumulate-t2 (a n)
  (declare (xargs :measure (nfix n)))
  (if (and (integerp n) (< 0 n))
      (+
       (ps14-t2 (ps14-shift a (- n 1)))
       (ps14-l-accumulate-t2 a (- n 1)))
    0))

(defun ps14-l-accumulate-a4 (a a1 i n)
  (declare (xargs :measure (nfix n)))
  (if (and (integerp n) (< 0 n))
      (+
       (ps14-a4-value
        a a1 i (ps14-shift a1 (- n 1)))
       (ps14-l-accumulate-a4 a a1 i (- n 1)))
    0))

;; Exact unfolding of Axiomatic1.p_accumulatebounds_1' over every
;; mathematical integer index.

(defun-sk ps14-accumulatebounds-t2-p (a1 upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= index upper)
      (implies
       (<= 0 index)
       (let
           ((partial
             (ps14-l-accumulate-t2 a1 index)))
         (and
          (<= -2147483648 partial)
          (<= partial 2147483647))))))))

;; Exact unfolding of Axiomatic.p_unchanged_1' for a_4 and t_2.

(defun-sk ps14-unchanged-a4-t2-p (a a1 i)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index i)
       (equal
        (ps14-t2 (ps14-shift a1 index))
        (ps14-a4-value
         a a1 i (ps14-shift a1 index))))))))

;; Exact unfolding of Axiomatic1.p_partialsum for a_4.

(defun-sk ps14-partialsum-a4-p (a a1 i i1)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index i1)
       (equal
        (ps14-a4-value a a1 i (ps14-shift a index))
        (ps14-l-accumulate-a4
         a a1 i (+ 1 index))))))))

(defun-sk
    ntp4vc-partial-sum-assert-rte-signed-overflow-2-goal14-statement
    ()
  (forall
   (a a1 i i1)
   (implies
    (and
     (ps14-address-p a)
     (ps14-address-p a1)
     (integerp i)
     (integerp i1)
     (ps14-function-types-p))
    (let*
        ((a2 (ps14-shift a 0))
         (a3 (ps14-shift a1 0))
         (x (ps14-t2 a3))
         (x1 (- i1 1))
         (a5
          (ps14-a4-value
           a a1 i (ps14-shift a x1)))
         (a6
          (ps14-a4-value
           a a1 i (ps14-shift a1 i1)))
         (a7
          (ps14-a4-value
           a a1 i
           (ps14-shift a (ps14-to-uint32 x1)))))
      (implies
       (and
        (equal
         a5
         (ps14-l-accumulate-a4 a a1 i i1))
        (< 0 i)
        (< 0 i1)
        (<= i1 i)
        (< i1 i)
        (<= (ps14-region (ps14-address-base a)) 0)
        (<= (ps14-region (ps14-address-base a1)) 0)
        (ps14-linked-p)
        (ps14-is-uint32-p i)
        (ps14-is-uint32-p i1)
        (ps14-is-sint32-p x)
        (ps14-valid-rd-p a3 1)
        (ps14-valid-rd-p a3 i)
        (ps14-valid-rw-p a2 1)
        (ps14-valid-rw-p a2 i)
        (ps14-accumulatebounds-t2-p a1 (+ 1 i))
        (ps14-separated-p a3 i a2 i)
        (ps14-is-sint32-p a6)
        (ps14-is-sint32-p a5)
        (ps14-is-sint32-p a7)
        (ps14-unchanged-a4-t2-p a a1 i)
        (ps14-partialsum-a4-p a a1 i i1))
       (<= (+ a6 a7) 2147483647))))))

(value-triple :itpeval-statement-checked)

:q
