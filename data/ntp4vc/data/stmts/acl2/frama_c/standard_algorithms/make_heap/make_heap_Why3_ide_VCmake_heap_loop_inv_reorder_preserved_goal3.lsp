;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/make_heap/make_heap_Why3_ide_VCmake_heap_loop_inv_reorder_preserved_goal3:
;; preservation of the make-heap multiset invariant after two havoc-based
;; memory updates under the stated bounds, validity, heap, unchanged-range,
;; linkedness, and prior multiset hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mhg3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mhg3-address-base (address)
  (car address))

(defun mhg3-address-offset (address)
  (cdr address))

(defun mhg3-shift (address amount)
  (cons
   (mhg3-address-base address)
   (+ (mhg3-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_2, t_3, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub mhg3-t1 (address) t)
(defstub mhg3-t2 (address) t)
(defstub mhg3-t3 (address) t)
(defstub mhg3-allocation (index) t)
(defstub mhg3-region (base) t)
(defstub mhg3-linked-op () t)

(defun-sk mhg3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mhg3-address-p address)
      (and
       (integerp (mhg3-t1 address))
       (integerp (mhg3-t2 address))
       (integerp (mhg3-t3 address))))
     (implies
      (integerp index)
      (integerp (mhg3-allocation index)))
     (implies
      (integerp base)
      (integerp (mhg3-region base))))))

(defun mhg3-linked-p ()
  (if (mhg3-linked-op) t nil))

(defun mhg3-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mhg3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mhg3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mhg3-address-base address))
    (<= 0 (mhg3-address-offset address))
    (<=
     (+ (mhg3-address-offset address) length)
     (mhg3-allocation (mhg3-address-base address))))))

(defun mhg3-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mhg3-address-base left)
     (mhg3-address-base right)))
   (<=
    (+ (mhg3-address-offset right) right-length)
    (mhg3-address-offset left))
   (<=
    (+ (mhg3-address-offset left) left-length)
    (mhg3-address-offset right))))

;; Exact pointwise values of
;; a_2 = havoc t_1 t_3 (shift a 0) i and
;; a_3 = havoc t_2 a_2 (shift a 0) (1 + i_1).

(defun mhg3-a2-read (query a i)
  (if
      (mhg3-separated-p
       query 1 (mhg3-shift a 0) i)
      (mhg3-t3 query)
    (mhg3-t1 query)))

(defun mhg3-a3-read (query a i i1)
  (let ((x (+ 1 i1)))
    (if
        (mhg3-separated-p
         query 1 (mhg3-shift a 0) x)
        (mhg3-a2-read query a i)
      (mhg3-t2 query))))

;; The three memory views occurring in the source occurrence-count predicate.

(defun mhg3-view-read (view query a i i1)
  (cond
   ((equal view 0)
    (mhg3-t3 query))
   ((equal view 1)
    (mhg3-a2-read query a i))
   (t
    (mhg3-a3-read query a i i1))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [first,last). These recursions give its exact characterization from the
;; source empty, hit, and miss equations.

(defun mhg3-count-span
    (view a i i1 first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (mhg3-view-read
           view
           (mhg3-shift a (+ first (1- span)))
           a i i1)
          value)
         1
       0)
     (mhg3-count-span
      view a i i1 first (1- span) value))))

(defun mhg3-count
    (view a i i1 first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (mhg3-count-span
       view a i i1 first (- last first) value)
    0))

;; Exact unfoldings of the heap, unchanged-range, and multiset predicates.
;; For positive child indices, floor((index - 1)/2) equals the source
;; truncating integer division used by l_heapparent.

(defun-sk mhg3-isheap-a2-p (a i upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< 0 index)
      (< index upper))
     (<=
      (mhg3-a2-read (mhg3-shift a index) a i)
      (mhg3-a2-read
       (mhg3-shift a (floor (- index 1) 2))
       a i)))))

(defun-sk mhg3-isheap-a3-p (a i i1 upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< 0 index)
      (< index upper))
     (<=
      (mhg3-a3-read (mhg3-shift a index) a i i1)
      (mhg3-a3-read
       (mhg3-shift a (floor (- index 1) 2))
       a i i1)))))

(defun-sk mhg3-unchanged-a2-t3-p
    (a i lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (mhg3-t3 (mhg3-shift a index))
      (mhg3-a2-read (mhg3-shift a index) a i)))))

(defun-sk mhg3-multiset-a2-t3-p
    (a i i1 first last)
  (forall (value)
    (implies
     (mhg3-is-sint32-p value)
     (equal
      (mhg3-count 0 a i i1 first last value)
      (mhg3-count 1 a i i1 first last value)))))

(defun-sk mhg3-multiset-a3-a2-p
    (a i i1 first last)
  (forall (value)
    (implies
     (mhg3-is-sint32-p value)
     (equal
      (mhg3-count 1 a i i1 first last value)
      (mhg3-count 2 a i i1 first last value)))))

(defun-sk mhg3-multiset-a3-t3-p
    (a i i1 first last)
  (forall (value)
    (implies
     (mhg3-is-sint32-p value)
     (equal
      (mhg3-count 0 a i i1 first last value)
      (mhg3-count 2 a i i1 first last value)))))

(defun-sk
    ntp4vc-make-heap-loop-inv-reorder-preserved-goal3-statement ()
  (forall
   (i1 a i)
   (implies
    (and
     (integerp i1)
     (mhg3-address-p a)
     (integerp i)
     (mhg3-function-types-p))
    (let*
        ((x (+ 1 i1))
         (a1 (mhg3-shift a 0)))
      (implies
       (and
        (< 0 i)
        (< 0 i1)
        (<= i1 i)
        (< i1 i)
        (<= (mhg3-region (mhg3-address-base a)) 0)
        (<= i1 4294967294)
        (mhg3-linked-p)
        (mhg3-is-uint32-p i)
        (mhg3-is-uint32-p i1)
        (mhg3-is-uint32-p x)
        (mhg3-valid-rw-p a1 i)
        (mhg3-valid-rw-p a1 x)
        (mhg3-isheap-a2-p a i i1)
        (mhg3-multiset-a2-t3-p a i i1 0 x)
        (mhg3-unchanged-a2-t3-p a i x i)
        (mhg3-isheap-a3-p a i i1 x)
       (mhg3-multiset-a3-a2-p a i i1 0 x))
       (mhg3-multiset-a3-t3-p
        a i i1 0 (+ 2 i1)))))))

(value-triple :itpeval-statement-checked)

:q
