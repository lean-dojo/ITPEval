;; Statement-only formalization of VERINA corpus artifact verina_advanced_37,
;; "majorityElement": insertion sorting an integer list and selecting its
;; middle entry returns the strict majority element under the stated
;; existence precondition. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-37-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-37-integer-listp (cdr xs)))
    (equal xs nil)))

;; This recursive count is the source List.count operation on integer lists.

(defun verina-advanced-37-list-count (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (+
       (if (equal value (car xs)) 1 0)
       (verina-advanced-37-list-count
        value
        (cdr xs)))
    0))

;; This predicate is List.any applied to the strict-majority test.

(defun verina-advanced-37-any-majority-p
    (remaining whole threshold)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (or
       (< threshold
          (verina-advanced-37-list-count
           (car remaining)
           whole))
       (verina-advanced-37-any-majority-p
        (cdr remaining)
        whole
        threshold))
    nil))

(defun verina-advanced-37-majority-element-precond (nums)
  (and
   (< 0 (len nums))
   (verina-advanced-37-any-majority-p
    nums
    nums
    (floor (len nums) 2))))

;; INSERT and INSERTION-SORT reproduce the source local recursive helpers.
;; The comparison is integer order, and equal elements are inserted before
;; the existing equal element exactly as in the Lean definition.

(defun verina-advanced-37-insert (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (let ((head (car xs))
            (tail (cdr xs)))
        (if (<= x head)
            (cons x (cons head tail))
          (cons
           head
           (verina-advanced-37-insert x tail))))
    (list x)))

(defun verina-advanced-37-insertion-sort (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (verina-advanced-37-insert
       (car xs)
       (verina-advanced-37-insertion-sort
        (cdr xs)))
    nil))

;; This is the source getAt based on List.drop: index zero returns the head,
;; and every missing index returns the integer default zero.

(defun verina-advanced-37-get-at (xs index)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (zp index)
          (car xs)
        (verina-advanced-37-get-at
         (cdr xs)
         (- index 1)))
    0))

;; The proof-valued precondition argument is computationally irrelevant.
;; Sorting, length computation, midpoint division, and lookup remain connected
;; exactly as in the source executable definition.

(defun verina-advanced-37-majority-element (nums)
  (let* ((sorted
          (verina-advanced-37-insertion-sort nums))
         (length (len sorted))
         (middle (floor length 2)))
    (verina-advanced-37-get-at sorted middle)))

;; This universal list recursion is the source List.all condition: every
;; input entry either equals RESULT or occurs at most half as often as the
;; list length.

(defun verina-advanced-37-all-result-or-nonmajority-p
    (remaining whole result threshold)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (or
        (equal (car remaining) result)
        (<=
         (verina-advanced-37-list-count
          (car remaining)
          whole)
         threshold))
       (verina-advanced-37-all-result-or-nonmajority-p
        (cdr remaining)
        whole
        result
        threshold))
    (equal remaining nil)))

(defun verina-advanced-37-majority-element-postcond
    (nums result)
  (let ((threshold (floor (len nums) 2)))
    (and
     (verina-advanced-37-integer-listp nums)
     (integerp result)
     (< threshold
        (verina-advanced-37-list-count result nums))
     (verina-advanced-37-all-result-or-nonmajority-p
      nums
      nums
      result
      threshold))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and complete source precondition;
;; its conclusion applies the complete postcondition to the executable result.

(defun verina-advanced-37-majority-element-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-37-integer-listp nums)
    (verina-advanced-37-majority-element-precond nums))
   (verina-advanced-37-majority-element-postcond
    nums
    (verina-advanced-37-majority-element nums))))

(value-triple :itpeval-statement-checked)
:q
