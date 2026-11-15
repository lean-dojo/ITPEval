;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_shearsort_Quicksort_quicksortqtvc: the top-level
;; quicksort verification condition for a globally sorted permutation of an
;; arbitrary finite integer list. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite ACL2 lists of unbounded ACL2 integers represent the source
;; arrays of mathematical integers without restricting lengths or values.

(defun shearsort-qs-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (shearsort-qs-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Int.toNat maps negative integers to zero. Source list indexing is total,
;; with the inhabited integer default zero outside the list.

(defun shearsort-qs-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun shearsort-qs-nth-int (index xs)
  (let ((natural-index
         (shearsort-qs-int-to-nat index)))
    (if (< natural-index (len xs))
        (nth natural-index xs)
      0)))

;; Natural drop, take, and half-open slice reproduce the operations in the
;; exported List.permut_sub' definition.

(defun shearsort-qs-drop (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      xs
    (shearsort-qs-drop
     (- count 1)
     (cdr xs))))

(defun shearsort-qs-take (count xs)
  (declare (xargs :measure (nfix count)))
  (if (or
       (zp count)
       (endp xs))
      nil
    (cons
     (car xs)
     (shearsort-qs-take
      (- count 1)
      (cdr xs)))))

(defun shearsort-qs-slice (xs lower upper)
  (shearsort-qs-take
   (nfix
    (-
     (nfix upper)
     (nfix lower)))
   (shearsort-qs-drop
    (nfix lower)
    xs)))

;; Removing one matching occurrence recursively gives finite-list multiset
;; permutation, equivalent to the source full-range permutation relation.

(defun shearsort-qs-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (equal value (car xs))
        (cdr xs)
      (cons
       (car xs)
       (shearsort-qs-remove-first
        value
        (cdr xs))))))

(defun shearsort-qs-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (endp right)
    (and
     (member-equal (car left) right)
     (shearsort-qs-permutation-p
      (cdr left)
      (shearsort-qs-remove-first
       (car left)
       right)))))

;; List.permut_sub' requires equal total lengths, unchanged prefix and suffix,
;; and a permutation of the selected half-open slice.

(defun shearsort-qs-permut-sub-prime-p
    (left right lower upper)
  (and
   (natp lower)
   (natp upper)
   (equal (len left) (len right))
   (equal
    (shearsort-qs-slice left 0 lower)
    (shearsort-qs-slice right 0 lower))
   (equal
    (shearsort-qs-slice
     left upper (len left))
    (shearsort-qs-slice
     right upper (len left)))
   (shearsort-qs-permutation-p
    (shearsort-qs-slice left lower upper)
    (shearsort-qs-slice right lower upper))))

;; The source sorted-subarray predicate quantifies over every pair of integer
;; indices in the half-open interval, including equal indices.

(defun-sk shearsort-qs-sorted-sub1-p
    (xs lower upper)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (integerp i2))
     (implies
      (and
       (<= lower i1)
       (<= i1 i2)
       (< i2 upper))
      (<=
       (shearsort-qs-nth-int i1 xs)
       (shearsort-qs-nth-int i2 xs))))))

(defun shearsort-qs-sorted-p (xs)
  (shearsort-qs-sorted-sub1-p
   xs 0 (len xs)))

;; A1 remains internally universally quantified. Its type, equal-length
;; condition, full-range sortedness, and full-range permutation are exactly
;; the postconditions supplied by the recursive quicksort call.

(defun-sk shearsort-qs-all-results-correct-p
    (a o1)
  (forall (a1)
    (implies
     (shearsort-qs-integer-list-p a1)
     (implies
      (equal (len a1) (len a))
      (implies
       (and
        (shearsort-qs-sorted-sub1-p
         a1 0 o1)
        (shearsort-qs-permut-sub-prime-p
         a a1 0
         (shearsort-qs-int-to-nat o1)))
       (and
        (shearsort-qs-sorted-p a1)
        (shearsort-qs-permutation-p
         a a1)))))))

(defun
    ntp4vc-pearl-verifythis-2021-shearsort-quicksort-quicksortqtvc-statement
    (a)
  (implies
   (shearsort-qs-integer-list-p a)
   (let ((o1 (len a)))
     (and
      (and
       (<= 0 0)
       (<= 0 o1)
       (<= o1 (len a)))
      (shearsort-qs-all-results-correct-p
       a o1)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
