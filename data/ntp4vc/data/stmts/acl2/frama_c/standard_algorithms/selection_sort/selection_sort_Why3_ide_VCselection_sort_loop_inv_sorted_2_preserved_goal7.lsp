;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/selection_sort_Why3_ide_VCselection_sort_loop_inv_sorted_2_preserved_goal7:
;; preservation of the selection-sort suffix lower-bound invariant after two
;; array point updates, under the stated bounds, validity, sortedness,
;; minimum-element, multiset, and unchanged-range hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ssg7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ssg7-address-base (address)
  (car address))

(defun ssg7-address-offset (address)
  (cdr address))

(defun ssg7-shift (address amount)
  (cons
   (ssg7-address-base address)
   (+ (ssg7-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub ssg7-t1 (address) t)
(defstub ssg7-t2 (address) t)
(defstub ssg7-allocation (index) t)
(defstub ssg7-region (base) t)
(defstub ssg7-linked-op () t)

(defun-sk ssg7-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (ssg7-address-p address)
      (and
       (integerp (ssg7-t1 address))
       (integerp (ssg7-t2 address))))
     (implies
      (integerp index)
      (integerp (ssg7-allocation index)))
     (implies
      (integerp base)
      (integerp (ssg7-region base))))))

(defun ssg7-linked-p ()
  (if (ssg7-linked-op) t nil))

(defun ssg7-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ssg7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun ssg7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ssg7-address-base address))
    (<= 0 (ssg7-address-offset address))
    (<=
     (+ (ssg7-address-offset address) length)
     (ssg7-allocation (ssg7-address-base address))))))

(defun ssg7-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (ssg7-address-base address)))
    (<= 0 (ssg7-address-offset address))
    (<=
     (+ (ssg7-address-offset address) length)
     (ssg7-allocation (ssg7-address-base address))))))

(defun ssg7-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (ssg7-address-base left)
     (ssg7-address-base right)))
   (<=
    (+ (ssg7-address-offset right) right-length)
    (ssg7-address-offset left))
   (<=
    (+ (ssg7-address-offset left) left-length)
    (ssg7-address-offset right))))

;; Exact pointwise value of
;; a_2 = havoc t_1 t_2 (shift a 0) i_2, using the source havoc_access
;; equation.

(defun ssg7-a2-read (query a i2)
  (if
      (ssg7-separated-p
       query 1 (ssg7-shift a 0) i2)
      (ssg7-t2 query)
    (ssg7-t1 query)))

;; Exact pointwise value of
;; a_6 = update (update a_2 a_3 i) a_4 a_5. The second update has
;; precedence when a_3 and a_4 coincide.

(defun ssg7-a6-read (query a i1 i2 i3 i)
  (let*
      ((a3 (ssg7-shift a i3))
       (a4 (ssg7-shift a i1))
       (a5 (ssg7-a2-read a3 a i2)))
    (if (equal query a4)
        a5
      (if (equal query a3)
          i
        (ssg7-a2-read query a i2)))))

;; The two memory views occurring in the occurrence-count hypothesis:
;; t_2 and a_2.

(defun ssg7-view-read (view query a i2)
  (if
      (equal view 0)
      (ssg7-t2 query)
    (ssg7-a2-read query a i2)))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun ssg7-count
    (view a i2 lower upper value)
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
              (ssg7-view-read
               view (ssg7-shift a last) a i2)
              value)
             1
           0)
         (ssg7-count
          view a i2 lower last value)))
    0))

;; Exact unfoldings of the source sortedness, lower-bound,
;; strict-lower-bound, unchanged-range, minimum-element, and
;; multiset-unchanged predicates over all mathematical integer indices and
;; all signed 32-bit values.

(defun-sk ssg7-sorted-a2-p (a lower upper i2)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (ssg7-a2-read (ssg7-shift a left) a i2)
      (ssg7-a2-read (ssg7-shift a right) a i2)))))

(defun-sk ssg7-lower-bound-a2-p
    (base lower upper value a i2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (ssg7-a2-read
       (ssg7-shift base index) a i2)))))

(defun-sk ssg7-lower-bound-a6-p
    (base lower upper value a i1 i2 i3 i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (ssg7-a6-read
       (ssg7-shift base index)
       a i1 i2 i3 i)))))

(defun-sk ssg7-strict-lower-bound-a2-p
    (base lower upper value a i2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      value
      (ssg7-a2-read
       (ssg7-shift base index) a i2)))))

(defun-sk ssg7-unchanged-a6-a2-p
    (a i1 i2 i3 i lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (ssg7-a2-read (ssg7-shift a index) a i2)
      (ssg7-a6-read
       (ssg7-shift a index) a i1 i2 i3 i)))))

(defun ssg7-minimum-element-a2-p
    (base upper minimum a i2)
  (and
   (<= 0 minimum)
   (< minimum upper)
   (ssg7-lower-bound-a2-p
    base 0 upper
    (ssg7-a2-read
     (ssg7-shift base minimum) a i2)
    a i2)))

(defun-sk ssg7-multiset-a2-t2-p
    (a i2 lower upper)
  (forall (value)
    (implies
     (ssg7-is-sint32-p value)
     (equal
      (ssg7-count 0 a i2 lower upper value)
      (ssg7-count 1 a i2 lower upper value)))))

(defun-sk
    ntp4vc-selection-sort-loop-inv-sorted-2-preserved-goal7-statement
    ()
  (forall
   (a i2 i3 i1 i)
   (implies
    (and
     (ssg7-address-p a)
     (integerp i2)
     (integerp i3)
     (integerp i1)
     (integerp i)
     (ssg7-function-types-p))
    (let*
        ((a1 (ssg7-shift a 0))
         (a3 (ssg7-shift a i3))
         (a4 (ssg7-shift a i1))
         (a5 (ssg7-a2-read a3 a i2))
         (a7 (ssg7-a6-read a3 a i1 i2 i3 i))
         (a8 (ssg7-a2-read a4 a i2))
         (x (+ 1 i3))
         (x2 (- i1 i3))
         (x3 (- i2 i3))
         (a9
          (ssg7-a2-read
           (ssg7-shift a (- i3 1)) a i2)))
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
        (<= (ssg7-region (ssg7-address-base a)) 0)
        (<= i3 4294967294)
        (<= i1 4294967295)
        (<= i2 (+ 4294967295 i3))
        (ssg7-linked-p)
        (ssg7-is-uint32-p i1)
        (ssg7-is-uint32-p i2)
        (ssg7-is-uint32-p i3)
        (ssg7-is-uint32-p x)
        (ssg7-is-uint32-p x2)
        (ssg7-is-sint32-p
         (ssg7-t2 (ssg7-shift a -1)))
        (ssg7-valid-rw-p a1 i2)
        (ssg7-valid-rd-p a3 x3)
        (ssg7-is-sint32-p a8)
        (ssg7-is-sint32-p a5)
        (ssg7-is-sint32-p a9)
        (ssg7-sorted-a2-p a 0 i3 i2)
        (ssg7-is-sint32-p a7)
        (ssg7-multiset-a2-t2-p a i2 0 i2)
        (ssg7-minimum-element-a2-p
         a3 x3 x2 a i2)
        (ssg7-strict-lower-bound-a2-p
         a3 0 x2 a8 a i2)
        (ssg7-unchanged-a6-a2-p
         a i1 i2 i3 i 0 i3)
        (ssg7-unchanged-a6-a2-p
         a i1 i2 i3 i (+ 1 i1) i2)
        (ssg7-unchanged-a6-a2-p
         a i1 i2 i3 i x i1)
        (implies
         (< 0 i3)
         (ssg7-lower-bound-a2-p
          a i3 i2 a9 a i2)))
       (ssg7-lower-bound-a6-p
        a x i2 a7 a i1 i2 i3 i))))))

(value-triple :itpeval-statement-checked)

:q
