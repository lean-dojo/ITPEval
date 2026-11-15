;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/make_heap/make_heap_Why3_ide_VCmake_heap_post_reorder_goal1:
;; preservation of the make-heap multiset property after a havoc-based memory
;; reorder, under the stated bounds, linkedness, write-validity, heap,
;; unchanged-range, and prior multiset hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mhpost1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mhpost1-address-base (address)
  (car address))

(defun mhpost1-address-offset (address)
  (cdr address))

(defun mhpost1-shift (address amount)
  (cons
   (mhpost1-address-base address)
   (+ (mhpost1-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_2, t_3, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub mhpost1-t1 (address) t)
(defstub mhpost1-t2 (address) t)
(defstub mhpost1-t3 (address) t)
(defstub mhpost1-allocation (index) t)
(defstub mhpost1-region (base) t)
(defstub mhpost1-linked-op () t)

(defun-sk mhpost1-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mhpost1-address-p address)
      (and
       (integerp (mhpost1-t1 address))
       (integerp (mhpost1-t2 address))
       (integerp (mhpost1-t3 address))))
     (implies
      (integerp index)
      (integerp (mhpost1-allocation index)))
     (implies
      (integerp base)
      (integerp (mhpost1-region base))))))

(defun mhpost1-linked-p ()
  (if (mhpost1-linked-op) t nil))

(defun mhpost1-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mhpost1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mhpost1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mhpost1-address-base address))
    (<= 0 (mhpost1-address-offset address))
    (<=
     (+ (mhpost1-address-offset address) length)
     (mhpost1-allocation
      (mhpost1-address-base address))))))

(defun mhpost1-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mhpost1-address-base left)
     (mhpost1-address-base right)))
   (<=
    (+ (mhpost1-address-offset right) right-length)
    (mhpost1-address-offset left))
   (<=
    (+ (mhpost1-address-offset left) left-length)
    (mhpost1-address-offset right))))

;; Exact pointwise value of havoc t_1 t_3 (shift a 0) length, using the
;; source havoc_access equation.

(defun mhpost1-havoc-read (a length query)
  (if
      (mhpost1-separated-p
       query 1 (mhpost1-shift a 0) length)
      (mhpost1-t3 query)
    (mhpost1-t1 query)))

;; Source equalities between addr -> int functions are represented
;; extensionally over every source address.

(defun-sk mhpost1-havoc-equals-t2-p (a length)
  (forall (query)
    (implies
     (mhpost1-address-p query)
     (equal
      (mhpost1-havoc-read a length query)
      (mhpost1-t2 query)))))

(defun-sk mhpost1-t3-equals-t2-p ()
  (forall (query)
    (implies
     (mhpost1-address-p query)
     (equal
      (mhpost1-t3 query)
      (mhpost1-t2 query)))))

;; A_Count.l_count_1' counts occurrences on [first,last). These recursions
;; give its exact finite-interval characterization from the source empty,
;; hit, and miss equations.

(defun mhpost1-count-t2-span
    (a first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (mhpost1-t2
           (mhpost1-shift a (+ first (1- span))))
          value)
         1
       0)
     (mhpost1-count-t2-span
      a first (1- span) value))))

(defun mhpost1-count-t2 (a first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (mhpost1-count-t2-span
       a first (- last first) value)
    0))

(defun mhpost1-count-t3-span
    (a first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (mhpost1-t3
           (mhpost1-shift a (+ first (1- span))))
          value)
         1
       0)
     (mhpost1-count-t3-span
      a first (1- span) value))))

(defun mhpost1-count-t3 (a first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (mhpost1-count-t3-span
       a first (- last first) value)
    0))

;; Exact unfoldings of the heap, unchanged-range, and multiset predicates
;; over all mathematical integer indices and all signed 32-bit values.

(defun-sk mhpost1-isheap-t2-p (a upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< 0 index)
      (< index upper))
     (<=
      (mhpost1-t2 (mhpost1-shift a index))
      (mhpost1-t2
       (mhpost1-shift
        a (floor (- index 1) 2)))))))

(defun-sk mhpost1-unchanged-t2-t3-p
    (a lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (mhpost1-t3 (mhpost1-shift a index))
      (mhpost1-t2 (mhpost1-shift a index))))))

(defun-sk mhpost1-multiset-t2-t3-p
    (a first last)
  (forall (value)
    (implies
     (mhpost1-is-sint32-p value)
     (equal
      (mhpost1-count-t3 a first last value)
      (mhpost1-count-t2 a first last value)))))

(defun-sk ntp4vc-make-heap-post-reorder-goal1-statement ()
  (forall
   (a i1 i p)
   (implies
    (and
     (mhpost1-address-p a)
     (integerp i1)
     (integerp i)
     (booleanp p)
     (mhpost1-function-types-p))
    (let*
        ((a1 (mhpost1-shift a 0))
         (x (+ 1 i1)))
      (implies
       (and
        (<=
         (mhpost1-region (mhpost1-address-base a))
         0)
        (mhpost1-linked-p)
        (mhpost1-is-uint32-p i)
        (mhpost1-is-uint32-p i1)
        (mhpost1-valid-rw-p a1 i)
        (if (< 0 i)
            (and
             (equal p nil)
             (mhpost1-havoc-equals-t2-p a i)
             (< 0 i1)
             (<= i1 i)
             (<= i i1)
             (mhpost1-isheap-t2-p a i1)
             (mhpost1-multiset-t2-t3-p
              a 0 x)
             (mhpost1-unchanged-t2-t3-p
              a x i))
          (mhpost1-t3-equals-t2-p)))
       (mhpost1-multiset-t2-t3-p
        a 0 i))))))

(value-triple :itpeval-statement-checked)

:q
