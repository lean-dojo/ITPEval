;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_post_reorder_goal1:
;; preservation of the insertion-sort multiset property after a havoc-based
;; memory reorder, under the stated bounds, linkedness, write-validity,
;; sortedness, unchanged-range, and prior multiset hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ispost1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ispost1-address-base (address)
  (car address))

(defun ispost1-address-offset (address)
  (cdr address))

(defun ispost1-shift (address amount)
  (cons
   (ispost1-address-base address)
   (+ (ispost1-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub ispost1-t1 (address) t)
(defstub ispost1-t2 (address) t)
(defstub ispost1-allocation (index) t)
(defstub ispost1-region (base) t)
(defstub ispost1-linked-op () t)

(defun-sk ispost1-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (ispost1-address-p address)
      (and
       (integerp (ispost1-t1 address))
       (integerp (ispost1-t2 address))))
     (implies
      (integerp index)
      (integerp (ispost1-allocation index)))
     (implies
      (integerp base)
      (integerp (ispost1-region base))))))

(defun ispost1-linked-p ()
  (if (ispost1-linked-op) t nil))

(defun ispost1-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ispost1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun ispost1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ispost1-address-base address))
    (<= 0 (ispost1-address-offset address))
    (<=
     (+ (ispost1-address-offset address) length)
     (ispost1-allocation (ispost1-address-base address))))))

(defun ispost1-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (ispost1-address-base left)
     (ispost1-address-base right)))
   (<=
    (+ (ispost1-address-offset right) right-length)
    (ispost1-address-offset left))
   (<=
    (+ (ispost1-address-offset left) left-length)
    (ispost1-address-offset right))))

;; Pointwise value of havoc t_1 t_2 (shift a 0) length, using the source
;; havoc_access equation.

(defun ispost1-havoc-read (a length query)
  (if
      (ispost1-separated-p
       query 1 (ispost1-shift a 0) length)
      (ispost1-t2 query)
    (ispost1-t1 query)))

;; A_Count.l_count_1' counts occurrences on [first,last). These recursions
;; give its exact finite-interval characterization from the source empty,
;; hit, and miss equations.

(defun ispost1-count-t2-span (a first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (ispost1-t2
           (ispost1-shift a (+ first (1- span))))
          value)
         1
       0)
     (ispost1-count-t2-span a first (1- span) value))))

(defun ispost1-count-t2 (a first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (ispost1-count-t2-span a first (- last first) value)
    0))

(defun ispost1-count-havoc-span
    (a length first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (ispost1-havoc-read
           a length
           (ispost1-shift a (+ first (1- span))))
          value)
         1
       0)
     (ispost1-count-havoc-span
      a length first (1- span) value))))

(defun ispost1-count-havoc
    (a length first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (ispost1-count-havoc-span
       a length first (- last first) value)
    0))

;; Exact unfoldings of the insertion-sort predicates over all mathematical
;; integer indices and all signed 32-bit values.

(defun-sk ispost1-sorted-havoc-p
    (a length lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (ispost1-havoc-read
       a length (ispost1-shift a left))
      (ispost1-havoc-read
       a length (ispost1-shift a right))))))

(defun-sk ispost1-unchanged-havoc-t2-p
    (a length lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (ispost1-t2 (ispost1-shift a index))
      (ispost1-havoc-read
       a length (ispost1-shift a index))))))

(defun-sk ispost1-multiset-havoc-t2-p
    (a length first last)
  (forall (value)
    (implies
     (and
      (integerp value)
      (ispost1-is-sint32-p value))
     (equal
      (ispost1-count-t2 a first last value)
      (ispost1-count-havoc
       a length first last value)))))

(defun-sk
    ntp4vc-insertion-sort-post-reorder-goal1-statement ()
  (forall
   (a i i1)
   (implies
    (and
     (ispost1-address-p a)
     (integerp i)
     (integerp i1)
     (ispost1-function-types-p))
    (let ((a1 (ispost1-shift a 0)))
      (implies
       (and
        (<= i1 i)
        (<= 0 i1)
        (<= i i1)
        (<=
         (ispost1-region (ispost1-address-base a))
         0)
        (ispost1-linked-p)
        (ispost1-is-uint32-p i)
        (ispost1-is-uint32-p i1)
        (ispost1-valid-rw-p a1 i)
        (ispost1-sorted-havoc-p a i 0 i1)
        (ispost1-unchanged-havoc-t2-p
         a i i1 i)
        (ispost1-multiset-havoc-t2-p
         a i 0 i1))
       (ispost1-multiset-havoc-t2-p
        a i1 0 i1))))))

(value-triple :itpeval-statement-checked)

:q
