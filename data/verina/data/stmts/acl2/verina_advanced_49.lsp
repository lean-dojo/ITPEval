;; Statement-only formalization of VERINA corpus artifact verina_advanced_49,
;; "mergeSortedLists": deterministic recursive merging of two nondecreasing
;; integer lists yields a nondecreasing permutation of their concatenation.
;; This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-49-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-49-integer-listp (cdr xs)))
    (equal xs nil)))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later element and recursively imposes the same condition on the tail.

(defun verina-advanced-49-head-at-most-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= x (car xs))
       (verina-advanced-49-head-at-most-all-p
        x
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-49-pairwise-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-49-head-at-most-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-49-pairwise-nondecreasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-49-merge-sorted-lists-precond
    (arr1 arr2)
  (and
   (verina-advanced-49-integer-listp arr1)
   (verina-advanced-49-integer-listp arr2)
   (verina-advanced-49-pairwise-nondecreasing-p arr1)
   (verina-advanced-49-pairwise-nondecreasing-p arr2)))

;; This recursion is the source's local MERGE helper. It compares both heads,
;; emits the left head on a tie, and otherwise advances exactly the list whose
;; head was emitted. The proof-valued precondition argument is erased.

(defun verina-advanced-49-merge (xs ys)
  (declare
   (xargs
    :measure
    (+ (acl2-count xs)
       (acl2-count ys))))
  (if (consp xs)
      (if (consp ys)
          (let ((x (car xs))
                (y (car ys)))
            (if (<= x y)
                (cons
                 x
                 (verina-advanced-49-merge
                  (cdr xs)
                  ys))
              (cons
               y
               (verina-advanced-49-merge
                xs
                (cdr ys)))))
        xs)
    ys))

(defun verina-advanced-49-merge-sorted-lists (arr1 arr2)
  (verina-advanced-49-merge arr1 arr2))

;; Removing one matching occurrence at each step gives exact finite-list
;; multiset equality, including multiplicities, and hence List.isPerm.

(defun verina-advanced-49-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (verina-advanced-49-remove-first
          value
          (cdr xs))))
    nil))

(defun verina-advanced-49-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-advanced-49-permutation-p
        (cdr left)
        (verina-advanced-49-remove-first
         (car left)
         right)))
    (equal right nil)))

(defun verina-advanced-49-merge-sorted-lists-postcond
    (arr1 arr2 result)
  (and
   (verina-advanced-49-integer-listp arr1)
   (verina-advanced-49-integer-listp arr2)
   (verina-advanced-49-integer-listp result)
   (verina-advanced-49-pairwise-nondecreasing-p result)
   (verina-advanced-49-permutation-p
    (append arr1 arr2)
    result)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent is the complete source precondition over the two List Int
;; inputs, and its conclusion applies the complete postcondition to the exact
;; executable merge result.

(defun
    verina-advanced-49-merge-sorted-lists-spec-satisfied-statement
    (arr1 arr2)
  (implies
   (verina-advanced-49-merge-sorted-lists-precond
    arr1
    arr2)
   (verina-advanced-49-merge-sorted-lists-postcond
    arr1
    arr2
    (verina-advanced-49-merge-sorted-lists
     arr1
     arr2))))

(value-triple :itpeval-statement-checked)
:q
