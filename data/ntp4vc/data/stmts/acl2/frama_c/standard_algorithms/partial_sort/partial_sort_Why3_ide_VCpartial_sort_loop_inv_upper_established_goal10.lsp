;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_loop_inv_upper_established_goal10:
;; establishment of the partial-sort loop's prefix upper-bound invariant after
;; a havoc-based memory update, under the stated index, memory-validity, heap,
;; multiset, signed-value, linkedness, and region hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun psu10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun psu10-address-base (address)
  (car address))

(defun psu10-address-offset (address)
  (cdr address))

(defun psu10-shift (address amount)
  (cons
   (psu10-address-base address)
   (+ (psu10-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub psu10-t1 (address) t)
(defstub psu10-t2 (address) t)
(defstub psu10-allocation (index) t)
(defstub psu10-region (base) t)
(defstub psu10-linked-op () t)

(defun-sk psu10-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (psu10-address-p address)
      (and
       (integerp (psu10-t1 address))
       (integerp (psu10-t2 address))))
     (implies
      (integerp index)
      (integerp (psu10-allocation index)))
     (implies
      (integerp base)
      (integerp (psu10-region base))))))

(defun psu10-linked-p ()
  (if (psu10-linked-op) t nil))

(defun psu10-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun psu10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun psu10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (psu10-address-base address))
    (<= 0 (psu10-address-offset address))
    (<=
     (+ (psu10-address-offset address) length)
     (psu10-allocation
      (psu10-address-base address))))))

(defun psu10-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (psu10-address-base left)
     (psu10-address-base right)))
   (<=
    (+ (psu10-address-offset right) right-length)
    (psu10-address-offset left))
   (<=
    (+ (psu10-address-offset left) left-length)
    (psu10-address-offset right))))

;; Exact pointwise value of
;; a_2 = havoc t_1 t_2 (shift a 0) i_1,
;; using the source havoc_access equation.

(defun psu10-a2-read (address a i1)
  (if
      (psu10-separated-p
       address 1 (psu10-shift a 0) i1)
      (psu10-t2 address)
    (psu10-t1 address)))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). View 0 is a_2 and view 1 is t_2. This recursion is the
;; exact characterization given by the source empty, hit, and miss equations.

(defun psu10-view-read (view address a i1)
  (if (equal view 0)
      (psu10-a2-read address a i1)
    (psu10-t2 address)))

(defun psu10-count
    (view a i1 lower upper value)
  (declare
   (xargs
    :measure (nfix (- upper lower))))
  (if
      (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (let ((last (- upper 1)))
        (+
         (if
             (equal
              (psu10-view-read
               view (psu10-shift a last) a i1)
              value)
             1
           0)
         (psu10-count
          view a i1 lower last value)))
    0))

;; Exact unfoldings of Axiomatic1.p_isheap,
;; Axiomatic1.p_multisetunchanged_1', and
;; Axiomatic1.p_upperbound_1'. All source quantifiers remain over every
;; mathematical integer.

(defun-sk psu10-isheap-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (psu10-a2-read (psu10-shift a child) a upper)
      (psu10-a2-read
       (psu10-shift
        a (floor (- child 1) 2))
       a upper)))))

(defun-sk psu10-multiset-unchanged-p (a first last)
  (forall (value)
    (implies
     (psu10-is-sint32-p value)
     (equal
      (psu10-count 1 a last first last value)
      (psu10-count 0 a last first last value)))))

(defun-sk psu10-upperbound-p
    (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (psu10-a2-read (psu10-shift a index) a upper)
      value))))

(defun-sk
    ntp4vc-partial-sort-loop-inv-upper-established-goal10-statement ()
  (forall
   (a i1 i)
   (implies
    (and
     (psu10-address-p a)
     (integerp i1)
     (integerp i)
     (psu10-function-types-p))
    (let*
        ((a1 (psu10-shift a 0))
         (a3 (psu10-a2-read a1 a i1)))
      (implies
       (and
        (< 0 i1)
        (<= i1 i)
        (<= 0 i1)
        (<=
         (psu10-region (psu10-address-base a))
         0)
        (psu10-linked-p)
        (psu10-is-uint32-p i)
        (psu10-is-uint32-p i1)
        (psu10-valid-rw-p a1 i)
        (psu10-valid-rw-p a1 i1)
        (psu10-is-sint32-p a3)
        (psu10-isheap-p a i1)
        (psu10-multiset-unchanged-p a 0 i1))
       (psu10-upperbound-p a 0 i1 a3))))))

(value-triple :itpeval-statement-checked)

:q
