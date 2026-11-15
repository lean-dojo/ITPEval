;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/sort_heap/sort_heap_Why3_ide_VCsort_heap_loop_inv_reorder_preserved_goal6:
;; preservation of the sort-heap multiset invariant after two havoc-based
;; memory updates, under the stated bounds, validity, heap, sortedness,
;; lower-bound, maximum-element, unchanged-range, linkedness, and prior
;; multiset hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun shg6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun shg6-address-base (address)
  (car address))

(defun shg6-address-offset (address)
  (cdr address))

(defun shg6-shift (address amount)
  (cons
   (shg6-address-base address)
   (+ (shg6-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_2, t_3, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub shg6-t1 (address) t)
(defstub shg6-t2 (address) t)
(defstub shg6-t3 (address) t)
(defstub shg6-allocation (index) t)
(defstub shg6-region (base) t)
(defstub shg6-linked-op () t)

(defun-sk shg6-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (shg6-address-p address)
      (and
       (integerp (shg6-t1 address))
       (integerp (shg6-t2 address))
       (integerp (shg6-t3 address))))
     (implies
      (integerp index)
      (integerp (shg6-allocation index)))
     (implies
      (integerp base)
      (integerp (shg6-region base))))))

(defun shg6-linked-p ()
  (if (shg6-linked-op) t nil))

(defun shg6-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun shg6-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Why3 integer division truncates toward zero.

(defun shg6-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun shg6-heap-parent (index)
  (shg6-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun shg6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (shg6-address-base address))
    (<= 0 (shg6-address-offset address))
    (<=
     (+ (shg6-address-offset address) length)
     (shg6-allocation (shg6-address-base address))))))

(defun shg6-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (shg6-address-base left)
     (shg6-address-base right)))
   (<=
    (+ (shg6-address-offset right) right-length)
    (shg6-address-offset left))
   (<=
    (+ (shg6-address-offset left) left-length)
    (shg6-address-offset right))))

;; Exact pointwise values of
;; a_2 = havoc t_1 t_3 (shift a 0) i and
;; a_3 = havoc t_2 a_2 (shift a 0) i_1.

(defun shg6-a2-read (query a i)
  (if
      (shg6-separated-p
       query 1 (shg6-shift a 0) i)
      (shg6-t3 query)
    (shg6-t1 query)))

(defun shg6-a3-read (query a i i1)
  (if
      (shg6-separated-p
       query 1 (shg6-shift a 0) i1)
      (shg6-a2-read query a i)
    (shg6-t2 query)))

;; The three memory views occurring in the source occurrence-count predicate:
;; t_3, a_2, and a_3.

(defun shg6-view-read (view query a i i1)
  (cond
   ((equal view 0)
    (shg6-t3 query))
   ((equal view 1)
    (shg6-a2-read query a i))
   (t
    (shg6-a3-read query a i i1))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [first,last). These recursions give its exact characterization from the
;; source empty, hit, and miss equations for signed 32-bit values.

(defun shg6-count-span
    (view a i i1 first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (shg6-view-read
           view
           (shg6-shift a (+ first (1- span)))
           a i i1)
          value)
         1
       0)
     (shg6-count-span
      view a i i1 first (1- span) value))))

(defun shg6-count
    (view a i i1 first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (shg6-count-span
       view a i i1 first (- last first) value)
    0))

;; Exact unfoldings of the source heap, sortedness, bound, unchanged-range,
;; maximum-element, and multiset predicates over all mathematical integer
;; indices and all signed 32-bit values.

(defun-sk shg6-isheap-t3-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (shg6-t3 (shg6-shift a child))
      (shg6-t3
       (shg6-shift
        a (shg6-heap-parent child)))))))

(defun-sk shg6-isheap-a2-p (a i upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (shg6-a2-read (shg6-shift a child) a i)
      (shg6-a2-read
       (shg6-shift
        a (shg6-heap-parent child))
       a i)))))

(defun-sk shg6-isheap-a3-p (a i i1 upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (shg6-a3-read
       (shg6-shift a child) a i i1)
      (shg6-a3-read
       (shg6-shift
        a (shg6-heap-parent child))
       a i i1)))))

(defun-sk shg6-sorted-a2-p
    (a lower upper i)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (shg6-a2-read
       (shg6-shift a left) a i)
      (shg6-a2-read
       (shg6-shift a right) a i)))))

(defun-sk shg6-lower-bound-a2-p
    (a lower upper value i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (shg6-a2-read
       (shg6-shift a index) a i)))))

(defun-sk shg6-upper-bound-a3-p
    (a lower upper value i i1)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (shg6-a3-read
       (shg6-shift a index) a i i1)
      value))))

(defun shg6-maximum-element-a3-p
    (a upper maximum i i1)
  (and
   (<= 0 maximum)
   (< maximum upper)
   (shg6-upper-bound-a3-p
    a 0 upper
    (shg6-a3-read
     (shg6-shift a maximum) a i i1)
    i i1)))

(defun-sk shg6-unchanged-a3-a2-p
    (a i i1 lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (shg6-a2-read
       (shg6-shift a index) a i)
      (shg6-a3-read
       (shg6-shift a index) a i i1)))))

(defun-sk shg6-multiset-a2-t3-p
    (a i i1 first last)
  (forall (value)
    (implies
     (shg6-is-sint32-p value)
     (equal
      (shg6-count 0 a i i1 first last value)
      (shg6-count 1 a i i1 first last value)))))

(defun-sk shg6-multiset-a3-a2-p
    (a i i1 first last)
  (forall (value)
    (implies
     (shg6-is-sint32-p value)
     (equal
      (shg6-count 1 a i i1 first last value)
      (shg6-count 2 a i i1 first last value)))))

(defun-sk shg6-multiset-a3-t3-p
    (a i i1 first last)
  (forall (value)
    (implies
     (shg6-is-sint32-p value)
     (equal
      (shg6-count 0 a i i1 first last value)
      (shg6-count 2 a i i1 first last value)))))

(defun-sk
    ntp4vc-sort-heap-loop-inv-reorder-preserved-goal6-statement ()
  (forall
   (a i i1)
   (implies
    (and
     (shg6-address-p a)
     (integerp i)
     (integerp i1)
     (shg6-function-types-p))
    (let*
        ((a1 (shg6-shift a 0))
         (x (- i1 1))
         (a4
          (shg6-a3-read
           (shg6-shift a x) a i i1))
         (a5 (shg6-a2-read a1 a i)))
      (implies
       (and
        (equal a4 a5)
        (< 0 i1)
        (<= i1 i)
        (<= 0 i1)
        (<= (shg6-region (shg6-address-base a)) 0)
        (<= 2 i1)
        (shg6-linked-p)
        (shg6-is-uint32-p i)
        (shg6-is-uint32-p i1)
        (shg6-isheap-t3-p a i)
        (shg6-is-sint32-p (shg6-t3 a1))
        (shg6-valid-rw-p a1 i)
        (shg6-is-sint32-p a5)
        (shg6-isheap-a2-p a i i1)
        (shg6-sorted-a2-p a i1 i i)
        (shg6-multiset-a2-t3-p a i i1 0 i)
        (shg6-lower-bound-a2-p
         a i1 i a5 i)
        (shg6-is-sint32-p
         (shg6-a3-read a1 a i i1))
        (shg6-is-sint32-p a4)
        (shg6-isheap-a3-p a i i1 x)
        (shg6-maximum-element-a3-p
         a i1 x i i1)
        (shg6-unchanged-a3-a2-p
         a i i1 i1 i)
        (shg6-multiset-a3-a2-p
         a i i1 0 i1))
       (shg6-multiset-a3-t3-p
        a i i1 0 i))))))

(value-triple :itpeval-statement-checked)

:q
