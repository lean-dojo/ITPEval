;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_stmt_post_5_goal24:
;; preservation of the signed-32 multiset on the prefix through the swap
;; index after the stated havoc and swap memory updates, under the index,
;; validity, heap, multiset, unchanged-range, bound, linkedness, region, and
;; value hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun psg24-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun psg24-address-base (address)
  (car address))

(defun psg24-address-offset (address)
  (cdr address))

(defun psg24-shift (address amount)
  (cons
   (psg24-address-base address)
   (+ (psg24-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_5, t_2, t_3, and t_4; allocation map t; region function; and
;; linked predicate specialized to t.

(defstub psg24-t1 (address) t)
(defstub psg24-t5 (address) t)
(defstub psg24-t2 (address) t)
(defstub psg24-t3 (address) t)
(defstub psg24-t4 (address) t)
(defstub psg24-allocation (index) t)
(defstub psg24-region (base) t)
(defstub psg24-linked-op () t)

(defun-sk psg24-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (psg24-address-p address)
      (and
       (integerp (psg24-t1 address))
       (integerp (psg24-t5 address))
       (integerp (psg24-t2 address))
       (integerp (psg24-t3 address))
       (integerp (psg24-t4 address))))
     (implies
      (integerp index)
      (integerp (psg24-allocation index)))
     (implies
      (integerp base)
      (integerp (psg24-region base))))))

(defun psg24-linked-p ()
  (if (psg24-linked-op) t nil))

(defun psg24-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun psg24-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun psg24-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (psg24-address-base address))
    (<= 0 (psg24-address-offset address))
    (<=
     (+ (psg24-address-offset address) length)
     (psg24-allocation (psg24-address-base address))))))

(defun psg24-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (psg24-address-base address)))
    (<= 0 (psg24-address-offset address))
    (<=
     (+ (psg24-address-offset address) length)
     (psg24-allocation (psg24-address-base address))))))

(defun psg24-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (psg24-address-base left)
     (psg24-address-base right)))
   (<=
    (+ (psg24-address-offset right) right-length)
    (psg24-address-offset left))
   (<=
    (+ (psg24-address-offset left) left-length)
    (psg24-address-offset right))))

;; Exact pointwise values supplied by the source havoc_access equation:
;; a_2 = havoc t_1 t_5 a_1 i_2,
;; a_3 = havoc t_2 a_2 a_1 i_1,
;; a_4 = havoc t_3 a_3 a_1 i_2, and
;; a_13 = havoc t_4 a_10 a_1 i_2.

(defun psg24-a2-read (address a i2)
  (if
      (psg24-separated-p
       address 1 (psg24-shift a 0) i2)
      (psg24-t5 address)
    (psg24-t1 address)))

(defun psg24-a3-read (address a i1 i2)
  (if
      (psg24-separated-p
       address 1 (psg24-shift a 0) i1)
      (psg24-a2-read address a i2)
    (psg24-t2 address)))

(defun psg24-a4-read (address a i1 i2)
  (if
      (psg24-separated-p
       address 1 (psg24-shift a 0) i2)
      (psg24-a3-read address a i1 i2)
    (psg24-t3 address)))

;; Function.update (Function.update a_4 a_8 i) a_5 a_9: the outer a_5
;; update has priority if a_5 and a_8 coincide.

(defun psg24-a10-read
    (address a i1 i2 i3 swap-value)
  (let*
      ((a5 (psg24-shift a (- i2 1)))
       (a8 (psg24-shift a i3))
       (a9 (psg24-a4-read a8 a i1 i2)))
    (if (equal address a5)
        a9
      (if (equal address a8)
          swap-value
        (psg24-a4-read address a i1 i2)))))

(defun psg24-a13-read
    (address a i1 i2 i3 swap-value)
  (if
      (psg24-separated-p
       address 1 (psg24-shift a 0) i2)
      (psg24-a10-read
       address a i1 i2 i3 swap-value)
    (psg24-t4 address)))

;; Tags name exactly the source memories used by the quantified predicates:
;; 1=t_5, 5=a_2, 6=a_3, 7=a_4, 8=a_10, and 9=a_13.

(defun psg24-memory-read
    (view address a i1 i2 i3 swap-value)
  (cond
   ((equal view 1)
    (psg24-t5 address))
   ((equal view 5)
    (psg24-a2-read address a i2))
   ((equal view 6)
    (psg24-a3-read address a i1 i2))
   ((equal view 7)
    (psg24-a4-read address a i1 i2))
   ((equal view 8)
    (psg24-a10-read
     address a i1 i2 i3 swap-value))
   ((equal view 9)
    (psg24-a13-read
     address a i1 i2 i3 swap-value))
   (t
    (psg24-t1 address))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is the exact characterization given by the
;; source empty, hit, and miss equations for signed-32 values.

(defun psg24-count
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
              (psg24-memory-read
               view
               (psg24-shift a last)
               a i1 i2 i3 swap-value)
              value)
             1
           0)
         (psg24-count
          view a i1 i2 i3 swap-value
          lower last value)))
    0))

;; Exact unfoldings of the source heap, unchanged-range, multiset, upper
;; bound, lower bound, maximum-element, and swapped-inside predicates. Every
;; typed source quantifier remains over all mathematical integers.

(defun-sk psg24-isheap-p
    (view a upper i1 i2 i3 swap-value)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (psg24-memory-read
       view
       (psg24-shift a child)
       a i1 i2 i3 swap-value)
      (psg24-memory-read
       view
       (psg24-shift
        a (floor (- child 1) 2))
       a i1 i2 i3 swap-value)))))

(defun-sk psg24-unchanged-p
    (first-view second-view a lower upper
                i1 i2 i3 swap-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (psg24-memory-read
       second-view
       (psg24-shift a index)
       a i1 i2 i3 swap-value)
      (psg24-memory-read
       first-view
       (psg24-shift a index)
       a i1 i2 i3 swap-value)))))

(defun-sk psg24-multiset-unchanged-p
    (first-view second-view a lower upper
                i1 i2 i3 swap-value)
  (forall (value)
    (implies
     (and
      (integerp value)
      (psg24-is-sint32-p value))
     (equal
      (psg24-count
       second-view a i1 i2 i3 swap-value
       lower upper value)
      (psg24-count
       first-view a i1 i2 i3 swap-value
       lower upper value)))))

(defun-sk psg24-upperbound-p
    (view a lower upper value i1 i2 i3 swap-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (psg24-memory-read
       view
       (psg24-shift a index)
       a i1 i2 i3 swap-value)
      value))))

(defun-sk psg24-lowerbound-p
    (view a lower upper value i1 i2 i3 swap-value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (psg24-memory-read
       view
       (psg24-shift a index)
       a i1 i2 i3 swap-value)))))

(defun psg24-maxelement-p
    (view a upper maximum i1 i2 i3 swap-value)
  (and
   (<= 0 maximum)
   (< maximum upper)
   (psg24-upperbound-p
    view a 0 upper
    (psg24-memory-read
     view
     (psg24-shift a maximum)
     a i1 i2 i3 swap-value)
    i1 i2 i3 swap-value)))

(defun psg24-swappedinside-p
    (first-view second-view a left right upper
                i1 i2 i3 swap-value)
  (let
      ((left-address (psg24-shift a left))
       (right-address (psg24-shift a right)))
    (and
     (equal
      (psg24-memory-read
       second-view left-address
       a i1 i2 i3 swap-value)
      (psg24-memory-read
       first-view right-address
       a i1 i2 i3 swap-value))
     (equal
      (psg24-memory-read
       second-view right-address
       a i1 i2 i3 swap-value)
      (psg24-memory-read
       first-view left-address
       a i1 i2 i3 swap-value))
     (<= 0 left)
     (< left right)
     (< right upper)
     (psg24-unchanged-p
      first-view second-view a 0 left
      i1 i2 i3 swap-value)
     (psg24-unchanged-p
      first-view second-view a (+ 1 left) right
      i1 i2 i3 swap-value)
     (psg24-unchanged-p
      first-view second-view a (+ 1 right) upper
      i1 i2 i3 swap-value))))

(defun-sk
    ntp4vc-partial-sort-stmt-post-5-goal24-statement ()
  (forall
   (a i2 i1 i3 swap-value)
   (implies
    (and
     (psg24-address-p a)
     (integerp i2)
     (integerp i1)
     (integerp i3)
     (integerp swap-value)
     (psg24-function-types-p))
    (let*
        ((a1 (psg24-shift a 0))
         (x (- i2 1))
         (a5 (psg24-shift a x))
         (a6 (psg24-a4-read a5 a i1 i2))
         (a7 (psg24-a3-read a1 a i1 i2))
         (a8 (psg24-shift a i3))
         (a9 (psg24-a4-read a8 a i1 i2))
         (a10-at-a8
          (psg24-a10-read
           a8 a i1 i2 i3 swap-value))
         (a12 (psg24-a3-read a8 a i1 i2))
         (x1 (+ 1 i3))
         (a14
          (psg24-a13-read
           a1 a i1 i2 i3 swap-value)))
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
         (psg24-region (psg24-address-base a))
         0)
        (< a12 a7)
        (psg24-linked-p)
        (psg24-is-uint32-p i1)
        (psg24-is-uint32-p i2)
        (psg24-is-uint32-p i3)
        (psg24-valid-rd-p a1 1)
        (psg24-valid-rd-p a8 1)
        (psg24-valid-rw-p a1 i1)
        (psg24-valid-rw-p a1 i2)
        (psg24-valid-rw-p a8 1)
        (psg24-valid-rw-p a5 1)
        (psg24-isheap-p
         5 a i2 i1 i2 i3 swap-value)
        (psg24-multiset-unchanged-p
         5 1 a 0 i2 i1 i2 i3 swap-value)
        (psg24-is-sint32-p a7)
        (psg24-is-sint32-p a12)
        (psg24-isheap-p
         6 a i2 i1 i2 i3 swap-value)
        (psg24-multiset-unchanged-p
         6 1 a 0 i3 i1 i2 i3 swap-value)
        (psg24-unchanged-p
         6 1 a i3 i1 i1 i2 i3 swap-value)
        (psg24-upperbound-p
         6 a 0 i2 a7 i1 i2 i3 swap-value)
        (psg24-lowerbound-p
         6 a i2 i3 a7 i1 i2 i3 swap-value)
        (psg24-is-sint32-p a9)
        (psg24-is-sint32-p a6)
        (psg24-isheap-p
         7 a x i1 i2 i3 swap-value)
        (psg24-is-sint32-p a10-at-a8)
        (psg24-multiset-unchanged-p
         7 1 a 0 x1 i1 i2 i3 swap-value)
        (psg24-multiset-unchanged-p
         7 6 a 0 i2 i1 i2 i3 swap-value)
        (psg24-maxelement-p
         7 a i2 x i1 i2 i3 swap-value)
        (psg24-isheap-p
         8 a x i1 i2 i3 swap-value)
        (psg24-multiset-unchanged-p
         8 7 a 0 x1 i1 i2 i3 swap-value)
        (psg24-unchanged-p
         8 7 a x1 i1 i1 i2 i3 swap-value)
        (psg24-swappedinside-p
         8 7 a x i3 x1 i1 i2 i3 swap-value)
        (psg24-is-sint32-p a14)
        (psg24-isheap-p
         9 a i2 i1 i2 i3 swap-value)
        (psg24-multiset-unchanged-p
         9 8 a 0 i2 i1 i2 i3 swap-value)
        (psg24-lowerbound-p
         9 a i2 x1 a14 i1 i2 i3 swap-value))
       (psg24-multiset-unchanged-p
        9 8 a 0 x1 i1 i2 i3 swap-value))))))

(value-triple :itpeval-statement-checked)

:q
