;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_stmt_post_goal25:
;; preservation of the signed-32 multiset on the prefix through index i_2
;; after the stated havoc memory updates, under the index, validity, heap,
;; multiset, unchanged-range, bound, linkedness, region, and value hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun psg25-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun psg25-address-base (address)
  (car address))

(defun psg25-address-offset (address)
  (cdr address))

(defun psg25-shift (address amount)
  (cons
   (psg25-address-base address)
   (+ (psg25-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_4, t_2, and t_3; allocation map t; region function; and linked
;; predicate specialized to t.

(defstub psg25-t1 (address) t)
(defstub psg25-t4 (address) t)
(defstub psg25-t2 (address) t)
(defstub psg25-t3 (address) t)
(defstub psg25-allocation (index) t)
(defstub psg25-region (base) t)
(defstub psg25-linked-op () t)

(defun-sk psg25-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (psg25-address-p address)
      (and
       (integerp (psg25-t1 address))
       (integerp (psg25-t4 address))
       (integerp (psg25-t2 address))
       (integerp (psg25-t3 address))))
     (implies
      (integerp index)
      (integerp (psg25-allocation index)))
     (implies
      (integerp base)
      (integerp (psg25-region base))))))

(defun psg25-linked-p ()
  (if (psg25-linked-op) t nil))

(defun psg25-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun psg25-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun psg25-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (psg25-address-base address))
    (<= 0 (psg25-address-offset address))
    (<=
     (+ (psg25-address-offset address) length)
     (psg25-allocation (psg25-address-base address))))))

(defun psg25-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (psg25-address-base address)))
    (<= 0 (psg25-address-offset address))
    (<=
     (+ (psg25-address-offset address) length)
     (psg25-allocation (psg25-address-base address))))))

(defun psg25-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (psg25-address-base left)
     (psg25-address-base right)))
   (<=
    (+ (psg25-address-offset right) right-length)
    (psg25-address-offset left))
   (<=
    (+ (psg25-address-offset left) left-length)
    (psg25-address-offset right))))

;; Exact pointwise values supplied by the source havoc_access equation:
;; a_2 = havoc t_1 t_4 a_1 i_1,
;; a_3 = havoc t_2 a_2 a_1 i, and
;; a_4 = havoc t_3 a_3 a_1 i_1.

(defun psg25-a2-read (address a i1)
  (if
      (psg25-separated-p
       address 1 (psg25-shift a 0) i1)
      (psg25-t4 address)
    (psg25-t1 address)))

(defun psg25-a3-read (address a i1 i)
  (if
      (psg25-separated-p
       address 1 (psg25-shift a 0) i)
      (psg25-a2-read address a i1)
    (psg25-t2 address)))

(defun psg25-a4-read (address a i1 i)
  (if
      (psg25-separated-p
       address 1 (psg25-shift a 0) i1)
      (psg25-a3-read address a i1 i)
    (psg25-t3 address)))

;; Tags name exactly the source memories used by the quantified predicates:
;; 1=t_1, 2=t_4, 3=t_2, 4=t_3, 5=a_2, 6=a_3, and 7=a_4.

(defun psg25-memory-read (view address a i1 i)
  (cond
   ((equal view 1)
    (psg25-t1 address))
   ((equal view 2)
    (psg25-t4 address))
   ((equal view 3)
    (psg25-t2 address))
   ((equal view 4)
    (psg25-t3 address))
   ((equal view 5)
    (psg25-a2-read address a i1))
   ((equal view 6)
    (psg25-a3-read address a i1 i))
   (t
    (psg25-a4-read address a i1 i))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun psg25-count
    (view a i1 i lower upper value)
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
              (psg25-memory-read
               view (psg25-shift a last) a i1 i)
              value)
             1
           0)
         (psg25-count
          view a i1 i lower last value)))
    0))

;; Exact unfoldings of the source heap, unchanged-range, multiset,
;; upper-bound, lower-bound, and maximum-element predicates. Every typed
;; source quantifier remains over all mathematical integers.

(defun-sk psg25-isheap-p (view a upper i1 i)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (psg25-memory-read
       view (psg25-shift a child) a i1 i)
      (psg25-memory-read
       view
       (psg25-shift
        a (floor (- child 1) 2))
       a i1 i)))))

(defun-sk psg25-unchanged-p
    (first-view second-view a lower upper i1 i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (psg25-memory-read
       second-view (psg25-shift a index) a i1 i)
      (psg25-memory-read
       first-view (psg25-shift a index) a i1 i)))))

(defun-sk psg25-multiset-unchanged-p
    (first-view second-view a lower upper i1 i)
  (forall (value)
    (implies
     (psg25-is-sint32-p value)
     (equal
      (psg25-count
       second-view a i1 i lower upper value)
      (psg25-count
       first-view a i1 i lower upper value)))))

(defun-sk psg25-upperbound-p
    (view a lower upper value i1 i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (psg25-memory-read
       view (psg25-shift a index) a i1 i)
      value))))

(defun-sk psg25-lowerbound-p
    (view a lower upper value i1 i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (psg25-memory-read
       view (psg25-shift a index) a i1 i)))))

(defun psg25-maxelement-p
    (view a upper maximum i1 i)
  (and
   (<= 0 maximum)
   (< maximum upper)
   (psg25-upperbound-p
    view a 0 upper
    (psg25-memory-read
     view (psg25-shift a maximum) a i1 i)
    i1 i)))

(defun-sk
    ntp4vc-partial-sort-stmt-post-goal25-statement ()
  (forall
   (a i1 i i2)
   (implies
    (and
     (psg25-address-p a)
     (integerp i1)
     (integerp i)
     (integerp i2)
     (psg25-function-types-p))
    (let*
        ((a1 (psg25-shift a 0))
         (x (- i1 1))
         (a5
          (psg25-a4-read
           (psg25-shift a x) a i1 i))
         (a6 (psg25-a3-read a1 a i1 i))
         (a7 (psg25-shift a i2))
         (a8 (psg25-a3-read a7 a i1 i)))
      (implies
       (and
        (equal a5 a6)
        (< 0 i1)
        (<= i1 i)
        (<= i2 i)
        (<= 0 i1)
        (< i2 i)
        (<= i1 i2)
        (<=
         (psg25-region (psg25-address-base a))
         0)
        (< a8 a6)
        (psg25-linked-p)
        (psg25-is-uint32-p i)
        (psg25-is-uint32-p i1)
        (psg25-is-uint32-p i2)
        (psg25-valid-rd-p a1 1)
        (psg25-valid-rd-p a7 1)
        (psg25-valid-rw-p a1 i)
        (psg25-valid-rw-p a1 i1)
        (psg25-isheap-p 5 a i1 i1 i)
        (psg25-multiset-unchanged-p
         5 2 a 0 i1 i1 i)
        (psg25-is-sint32-p a6)
        (psg25-is-sint32-p a8)
        (psg25-isheap-p 6 a i1 i1 i)
        (psg25-multiset-unchanged-p
         6 2 a 0 i2 i1 i)
        (psg25-unchanged-p
         6 2 a i2 i i1 i)
        (psg25-upperbound-p
         6 a 0 i1 a6 i1 i)
        (psg25-lowerbound-p
         6 a i1 i2 a6 i1 i)
        (psg25-is-sint32-p a5)
        (psg25-isheap-p 7 a x i1 i)
        (psg25-multiset-unchanged-p
         7 6 a 0 i1 i1 i)
        (psg25-maxelement-p
         7 a i1 x i1 i))
       (psg25-multiset-unchanged-p
        7 2 a 0 (+ 1 i2) i1 i))))))

(value-triple :itpeval-statement-checked)

:q
