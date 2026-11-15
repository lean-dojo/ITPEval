;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_stmt_post_4_goal22:
;; preservation of the signed-32 multiset on the updated partial-sort prefix
;; after the stated havoc and swap memory updates, under the index, validity,
;; heap, multiset, unchanged-range, bound, linkedness, region, and value
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun psg22-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun psg22-address-base (address)
  (car address))

(defun psg22-address-offset (address)
  (cdr address))

(defun psg22-shift (address amount)
  (cons
   (psg22-address-base address)
   (+ (psg22-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_4, t_2, and t_3; allocation map t; region function; and linked
;; predicate specialized to t.

(defstub psg22-t1 (address) t)
(defstub psg22-t4 (address) t)
(defstub psg22-t2 (address) t)
(defstub psg22-t3 (address) t)
(defstub psg22-allocation (index) t)
(defstub psg22-region (base) t)
(defstub psg22-linked-op () t)

(defun-sk psg22-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (psg22-address-p address)
      (and
       (integerp (psg22-t1 address))
       (integerp (psg22-t4 address))
       (integerp (psg22-t2 address))
       (integerp (psg22-t3 address))))
     (implies
      (integerp index)
      (integerp (psg22-allocation index)))
     (implies
      (integerp base)
      (integerp (psg22-region base))))))

(defun psg22-linked-p ()
  (if (psg22-linked-op) t nil))

(defun psg22-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun psg22-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun psg22-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (psg22-address-base address))
    (<= 0 (psg22-address-offset address))
    (<=
     (+ (psg22-address-offset address) length)
     (psg22-allocation (psg22-address-base address))))))

(defun psg22-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (psg22-address-base address)))
    (<= 0 (psg22-address-offset address))
    (<=
     (+ (psg22-address-offset address) length)
     (psg22-allocation (psg22-address-base address))))))

(defun psg22-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (psg22-address-base left)
     (psg22-address-base right)))
   (<=
    (+ (psg22-address-offset right) right-length)
    (psg22-address-offset left))
   (<=
    (+ (psg22-address-offset left) left-length)
    (psg22-address-offset right))))

;; Exact pointwise values supplied by the source havoc_access equation:
;; a_2 = havoc t_1 t_4 a_1 i_2,
;; a_3 = havoc t_2 a_2 a_1 i_1, and
;; a_4 = havoc t_3 a_3 a_1 i_2.

(defun psg22-a2-read (address a i2)
  (if
      (psg22-separated-p
       address 1 (psg22-shift a 0) i2)
      (psg22-t4 address)
    (psg22-t1 address)))

(defun psg22-a3-read (address a i1 i2)
  (if
      (psg22-separated-p
       address 1 (psg22-shift a 0) i1)
      (psg22-a2-read address a i2)
    (psg22-t2 address)))

(defun psg22-a4-read (address a i1 i2)
  (if
      (psg22-separated-p
       address 1 (psg22-shift a 0) i2)
      (psg22-a3-read address a i1 i2)
    (psg22-t3 address)))

;; Function.update (Function.update a_4 a_8 i) a_5 a_9: the outer a_5
;; update has priority if a_5 and a_8 coincide.

(defun psg22-a10-read
    (address a i1 i2 i3 swap-value)
  (let*
      ((a5 (psg22-shift a (- i2 1)))
       (a8 (psg22-shift a i3))
       (a9 (psg22-a4-read a8 a i1 i2)))
    (if (equal address a5)
        a9
      (if (equal address a8)
          swap-value
        (psg22-a4-read address a i1 i2)))))

;; Tags name exactly the source memories used by the quantified predicates:
;; 1=t_4, 2=a_2, 3=a_3, 4=a_4, and 10=a_10.

(defun psg22-memory-read
    (view address a i1 i2 i3 swap-value)
  (cond
   ((equal view 1)
    (psg22-t4 address))
   ((equal view 2)
    (psg22-a2-read address a i2))
   ((equal view 3)
    (psg22-a3-read address a i1 i2))
   ((equal view 4)
    (psg22-a4-read address a i1 i2))
   ((equal view 10)
    (psg22-a10-read
     address a i1 i2 i3 swap-value))
   (t
    (psg22-t1 address))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is the exact characterization given by the
;; source empty, hit, and miss equations for signed-32 values.

(defun psg22-count
    (view a i1 i2 i3 swap-value lower upper value)
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
              (psg22-memory-read
               view
               (psg22-shift a last)
               a i1 i2 i3 swap-value)
              value)
             1
           0)
         (psg22-count
          view a i1 i2 i3 swap-value
          lower last value)))
    0))

;; Exact unfoldings of the source heap, unchanged-range, multiset, upper
;; bound, lower bound, maximum-element, and swapped-inside predicates. Every
;; typed source quantifier remains over all mathematical integers.

(defun-sk psg22-isheap-p
    (view a upper i1 i2 i3 swap-value)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (psg22-memory-read
       view
       (psg22-shift a child)
       a i1 i2 i3 swap-value)
      (psg22-memory-read
       view
       (psg22-shift
        a (floor (- child 1) 2))
       a i1 i2 i3 swap-value)))))

(defun-sk psg22-unchanged-p
    (first-view second-view a lower upper
                i1 i2 i3 swap-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (psg22-memory-read
       second-view
       (psg22-shift a index)
       a i1 i2 i3 swap-value)
      (psg22-memory-read
       first-view
       (psg22-shift a index)
       a i1 i2 i3 swap-value)))))

(defun-sk psg22-multiset-unchanged-p
    (first-view second-view a lower upper
                i1 i2 i3 swap-value)
  (forall (value)
    (implies
     (and
      (integerp value)
      (psg22-is-sint32-p value))
     (equal
      (psg22-count
       second-view a i1 i2 i3 swap-value
       lower upper value)
      (psg22-count
       first-view a i1 i2 i3 swap-value
       lower upper value)))))

(defun-sk psg22-upperbound-p
    (view a lower upper value i1 i2 i3 swap-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (psg22-memory-read
       view
       (psg22-shift a index)
       a i1 i2 i3 swap-value)
      value))))

(defun-sk psg22-lowerbound-p
    (view a lower upper value i1 i2 i3 swap-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (psg22-memory-read
       view
       (psg22-shift a index)
       a i1 i2 i3 swap-value)))))

(defun psg22-maxelement-p
    (view a upper maximum i1 i2 i3 swap-value)
  (and
   (<= 0 maximum)
   (< maximum upper)
   (psg22-upperbound-p
    view a 0 upper
    (psg22-memory-read
     view
     (psg22-shift a maximum)
     a i1 i2 i3 swap-value)
    i1 i2 i3 swap-value)))

(defun psg22-swappedinside-p
    (first-view second-view a left right upper
                i1 i2 i3 swap-value)
  (let
      ((left-address (psg22-shift a left))
       (right-address (psg22-shift a right)))
    (and
     (equal
      (psg22-memory-read
       second-view left-address
       a i1 i2 i3 swap-value)
      (psg22-memory-read
       first-view right-address
       a i1 i2 i3 swap-value))
     (equal
      (psg22-memory-read
       second-view right-address
       a i1 i2 i3 swap-value)
      (psg22-memory-read
       first-view left-address
       a i1 i2 i3 swap-value))
     (<= 0 left)
     (< left right)
     (< right upper)
     (psg22-unchanged-p
      first-view second-view a 0 left
      i1 i2 i3 swap-value)
     (psg22-unchanged-p
      first-view second-view a (+ 1 left) right
      i1 i2 i3 swap-value)
     (psg22-unchanged-p
      first-view second-view a (+ 1 right) upper
      i1 i2 i3 swap-value))))

(defun-sk
    ntp4vc-partial-sort-stmt-post-4-goal22-statement ()
  (forall
   (a i2 i1 i3 swap-value)
   (implies
    (and
     (psg22-address-p a)
     (integerp i2)
     (integerp i1)
     (integerp i3)
     (integerp swap-value)
     (psg22-function-types-p))
    (let*
        ((a1 (psg22-shift a 0))
         (x (- i2 1))
         (a5 (psg22-shift a x))
         (a6 (psg22-a4-read a5 a i1 i2))
         (a7 (psg22-a3-read a1 a i1 i2))
         (a8 (psg22-shift a i3))
         (a9 (psg22-a4-read a8 a i1 i2))
         (a10-at-a8
          (psg22-a10-read
           a8 a i1 i2 i3 swap-value))
         (a12 (psg22-a3-read a8 a i1 i2))
         (x1 (+ 1 i3)))
      (implies
       (and
        (equal a6 a7)
        (equal a10-at-a8 a6)
        (< 0 i2)
        (<= i2 i1)
        (<= i3 i1)
        (<= 0 i2)
        (< i3 i1)
        (<= i2 i3)
        (<=
         (psg22-region (psg22-address-base a))
         0)
        (< a12 a7)
        (psg22-linked-p)
        (psg22-is-uint32-p i1)
        (psg22-is-uint32-p i2)
        (psg22-is-uint32-p i3)
        (psg22-valid-rd-p a1 1)
        (psg22-valid-rd-p a8 1)
        (psg22-valid-rw-p a1 i1)
        (psg22-valid-rw-p a1 i2)
        (psg22-valid-rw-p a8 1)
        (psg22-valid-rw-p a5 1)
        (psg22-isheap-p
         2 a i2 i1 i2 i3 swap-value)
        (psg22-multiset-unchanged-p
         2 1 a 0 i2 i1 i2 i3 swap-value)
        (psg22-is-sint32-p a7)
        (psg22-is-sint32-p a12)
        (psg22-isheap-p
         3 a i2 i1 i2 i3 swap-value)
        (psg22-multiset-unchanged-p
         3 1 a 0 i3 i1 i2 i3 swap-value)
        (psg22-unchanged-p
         3 1 a i3 i1 i1 i2 i3 swap-value)
        (psg22-upperbound-p
         3 a 0 i2 a7 i1 i2 i3 swap-value)
        (psg22-lowerbound-p
         3 a i2 i3 a7 i1 i2 i3 swap-value)
        (psg22-is-sint32-p a9)
        (psg22-is-sint32-p a6)
        (psg22-isheap-p
         4 a x i1 i2 i3 swap-value)
        (psg22-is-sint32-p a10-at-a8)
        (psg22-multiset-unchanged-p
         4 1 a 0 x1 i1 i2 i3 swap-value)
        (psg22-multiset-unchanged-p
         4 3 a 0 i2 i1 i2 i3 swap-value)
        (psg22-maxelement-p
         4 a i2 x i1 i2 i3 swap-value)
        (psg22-unchanged-p
         10 4 a x1 i1 i1 i2 i3 swap-value)
        (psg22-swappedinside-p
         10 4 a x i3 x1 i1 i2 i3 swap-value))
       (psg22-multiset-unchanged-p
        10 4 a 0 x1 i1 i2 i3 swap-value))))))

(value-triple :itpeval-statement-checked)

:q
