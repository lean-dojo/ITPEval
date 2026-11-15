;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/selection_sort_Why3_ide_VCselection_sort_loop_inv_reorder_preserved_goal3:
;; preservation of the selection-sort multiset invariant after two array
;; point updates, under the stated bounds, validity, sortedness, minimum,
;; lower-bound, unchanged-range, linkedness, and prior multiset hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ssg3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ssg3-address-base (address)
  (car address))

(defun ssg3-address-offset (address)
  (cdr address))

(defun ssg3-shift (address amount)
  (cons
   (ssg3-address-base address)
   (+ (ssg3-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub ssg3-t1 (address) t)
(defstub ssg3-t2 (address) t)
(defstub ssg3-allocation (index) t)
(defstub ssg3-region (base) t)
(defstub ssg3-linked-op () t)

(defun-sk ssg3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (ssg3-address-p address)
      (and
       (integerp (ssg3-t1 address))
       (integerp (ssg3-t2 address))))
     (implies
      (integerp index)
      (integerp (ssg3-allocation index)))
     (implies
      (integerp base)
      (integerp (ssg3-region base))))))

(defun ssg3-linked-p ()
  (if (ssg3-linked-op) t nil))

(defun ssg3-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ssg3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun ssg3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ssg3-address-base address))
    (<= 0 (ssg3-address-offset address))
    (<=
     (+ (ssg3-address-offset address) length)
     (ssg3-allocation (ssg3-address-base address))))))

(defun ssg3-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (ssg3-address-base address)))
    (<= 0 (ssg3-address-offset address))
    (<=
     (+ (ssg3-address-offset address) length)
     (ssg3-allocation (ssg3-address-base address))))))

(defun ssg3-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (ssg3-address-base left)
     (ssg3-address-base right)))
   (<=
    (+ (ssg3-address-offset right) right-length)
    (ssg3-address-offset left))
   (<=
    (+ (ssg3-address-offset left) left-length)
    (ssg3-address-offset right))))

;; Exact pointwise value of
;; a_2 = havoc t_1 t_2 (shift a 0) i_2, using the source havoc_access
;; equation.

(defun ssg3-a2-read (query a i2)
  (if
      (ssg3-separated-p
       query 1 (ssg3-shift a 0) i2)
      (ssg3-t2 query)
    (ssg3-t1 query)))

;; Exact pointwise value of
;; a_6 = update (update a_2 a_3 i) a_4 a_5. The second update has
;; precedence when a_3 and a_4 coincide.

(defun ssg3-a6-read (query a i1 i2 i3 i)
  (let*
      ((a3 (ssg3-shift a i3))
       (a4 (ssg3-shift a i1))
       (a5 (ssg3-a2-read a3 a i2)))
    (if (equal query a4)
        a5
      (if (equal query a3)
          i
        (ssg3-a2-read query a i2)))))

;; The three memory views occurring in the occurrence-count predicates:
;; t_2, a_2, and a_6.

(defun ssg3-view-read
    (view query a i1 i2 i3 i)
  (cond
   ((equal view 0)
    (ssg3-t2 query))
   ((equal view 1)
    (ssg3-a2-read query a i2))
   (t
    (ssg3-a6-read query a i1 i2 i3 i))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun ssg3-count
    (view a i1 i2 i3 i lower upper value)
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
              (ssg3-view-read
               view
               (ssg3-shift a last)
               a i1 i2 i3 i)
              value)
             1
           0)
         (ssg3-count
          view a i1 i2 i3 i
          lower last value)))
    0))

;; Exact unfoldings of the source sortedness, bounds, unchanged-range,
;; minimum-element, and multiset-unchanged predicates over all mathematical
;; integer indices and all signed 32-bit values.

(defun-sk ssg3-sorted-a2-p (a lower upper i2)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (ssg3-a2-read (ssg3-shift a left) a i2)
      (ssg3-a2-read (ssg3-shift a right) a i2)))))

(defun-sk ssg3-lower-bound-a2-p
    (base lower upper value a i2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (ssg3-a2-read
       (ssg3-shift base index) a i2)))))

(defun-sk ssg3-strict-lower-bound-a2-p
    (base lower upper value a i2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      value
      (ssg3-a2-read
       (ssg3-shift base index) a i2)))))

(defun-sk ssg3-unchanged-a6-a2-p
    (a i1 i2 i3 i lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (ssg3-a2-read (ssg3-shift a index) a i2)
      (ssg3-a6-read
       (ssg3-shift a index) a i1 i2 i3 i)))))

(defun ssg3-minimum-element-a2-p
    (base upper minimum a i2)
  (and
   (<= 0 minimum)
   (< minimum upper)
   (ssg3-lower-bound-a2-p
    base 0 upper
    (ssg3-a2-read
     (ssg3-shift base minimum) a i2)
    a i2)))

(defun-sk ssg3-multiset-a2-t2-p
    (a i1 i2 i3 i lower upper)
  (forall (value)
    (implies
     (ssg3-is-sint32-p value)
     (equal
      (ssg3-count
       0 a i1 i2 i3 i lower upper value)
      (ssg3-count
       1 a i1 i2 i3 i lower upper value)))))

(defun-sk ssg3-multiset-a6-t2-p
    (a i1 i2 i3 i lower upper)
  (forall (value)
    (implies
     (ssg3-is-sint32-p value)
     (equal
      (ssg3-count
       0 a i1 i2 i3 i lower upper value)
      (ssg3-count
       2 a i1 i2 i3 i lower upper value)))))

(defun-sk
    ntp4vc-selection-sort-loop-inv-reorder-preserved-goal3-statement
    ()
  (forall
   (a i2 i3 i1 i)
   (implies
    (and
     (ssg3-address-p a)
     (integerp i2)
     (integerp i3)
     (integerp i1)
     (integerp i)
     (ssg3-function-types-p))
    (let*
        ((a1 (ssg3-shift a 0))
         (a3 (ssg3-shift a i3))
         (a4 (ssg3-shift a i1))
         (a5 (ssg3-a2-read a3 a i2))
         (a7 (ssg3-a6-read a3 a i1 i2 i3 i))
         (a8 (ssg3-a2-read a4 a i2))
         (x1 (- i1 i3))
         (x2 (- i2 i3))
         (a9
          (ssg3-a2-read
           (ssg3-shift a (- i3 1)) a i2)))
      (implies
       (and
        (equal a7 a8)
        (<= 0 i1)
        (< i1 i2)
        (<= i3 i1)
        (<= i1 i2)
        (<= i3 i2)
        (<= 0 i3)
        (< i3 i2)
        (<= (ssg3-region (ssg3-address-base a)) 0)
        (<= i3 4294967294)
        (<= i1 4294967295)
        (<= i2 (+ 4294967295 i3))
        (ssg3-linked-p)
        (ssg3-is-uint32-p i1)
        (ssg3-is-uint32-p i2)
        (ssg3-is-uint32-p i3)
        (ssg3-is-uint32-p x1)
        (ssg3-is-sint32-p
         (ssg3-t2 (ssg3-shift a -1)))
        (ssg3-valid-rw-p a1 i2)
        (ssg3-valid-rd-p a3 x2)
        (ssg3-is-sint32-p a8)
        (ssg3-is-sint32-p a5)
        (ssg3-is-sint32-p a9)
        (ssg3-sorted-a2-p a 0 i3 i2)
        (ssg3-is-sint32-p a7)
        (ssg3-multiset-a2-t2-p
         a i1 i2 i3 i 0 i2)
        (ssg3-minimum-element-a2-p
         a3 x2 x1 a i2)
        (ssg3-strict-lower-bound-a2-p
         a3 0 x1 a8 a i2)
        (ssg3-unchanged-a6-a2-p
         a i1 i2 i3 i 0 i3)
        (ssg3-unchanged-a6-a2-p
         a i1 i2 i3 i (+ 1 i1) i2)
        (ssg3-unchanged-a6-a2-p
         a i1 i2 i3 i (+ 1 i3) i1)
        (implies
         (< 0 i3)
         (ssg3-lower-bound-a2-p
          a i3 i2 a9 a i2)))
       (ssg3-multiset-a6-t2-p
        a i1 i2 i3 i 0 i2))))))

(value-triple :itpeval-statement-checked)

:q
