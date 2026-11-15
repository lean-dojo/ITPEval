;; Statement-only formalization of VERINA corpus artifact verina_advanced_50,
;; "mergeSorted": the indexed merge loop and drain operations merge two
;; nondecreasing arrays of natural numbers into a sorted permutation of their
;; concatenation. This file contains no proof.

(in-package "ACL2")

;; A Lean Array Nat is represented exactly by its finite sequence of entries,
;; namely an ACL2 true list whose elements are natural numbers.

(defun verina-advanced-50-nat-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (natp (car xs))
       (verina-advanced-50-nat-listp (cdr xs)))
    (equal xs nil)))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later entry and recursively imposes the same condition on the tail.

(defun verina-advanced-50-head-at-most-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= x (car xs))
       (verina-advanced-50-head-at-most-all-p
        x
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-50-pairwise-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-50-head-at-most-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-50-pairwise-nondecreasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-50-merge-sorted-precond (a1 a2)
  (and
   (verina-advanced-50-nat-listp a1)
   (verina-advanced-50-nat-listp a2)
   (verina-advanced-50-pairwise-nondecreasing-p a1)
   (verina-advanced-50-pairwise-nondecreasing-p a2)))

;; This structural worker is the exact transition system of mergeLoop after
;; dropping the already-consumed prefixes. Array.push is represented by
;; appending one entry, so RESULT has the same order as the source array.

(defun verina-advanced-50-merge-loop-suffixes
    (xs ys i j result)
  (declare
   (xargs
    :measure
    (+ (acl2-count xs)
       (acl2-count ys))))
  (if (and (consp xs) (consp ys))
      (if (<= (car xs) (car ys))
          (verina-advanced-50-merge-loop-suffixes
           (cdr xs)
           ys
           (+ 1 i)
           j
           (append result (list (car xs))))
        (verina-advanced-50-merge-loop-suffixes
         xs
         (cdr ys)
         i
         (+ 1 j)
         (append result (list (car ys)))))
    (list i j result)))

(defun verina-advanced-50-merge-loop
    (a1 a2 i j result)
  (verina-advanced-50-merge-loop-suffixes
   (nthcdr (nfix i) a1)
   (nthcdr (nfix j) a2)
   (nfix i)
   (nfix j)
   result))

;; This worker and wrapper preserve drain: append every array entry from index
;; I onward to RESULT, in increasing index order.

(defun verina-advanced-50-drain-suffix (remaining result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-50-drain-suffix
       (cdr remaining)
       (append result (list (car remaining))))
    result))

(defun verina-advanced-50-drain (arr i result)
  (verina-advanced-50-drain-suffix
   (nthcdr (nfix i) arr)
   result))

;; The proof-valued precondition argument is computationally irrelevant. This
;; definition otherwise follows mergeSorted exactly: run mergeLoop from empty
;; state, drain A1, then drain A2.

(defun verina-advanced-50-merge-sorted (a1 a2)
  (let* ((state
          (verina-advanced-50-merge-loop
           a1 a2 0 0 nil))
         (i (car state))
         (j (cadr state))
         (result0 (caddr state))
         (result1
          (verina-advanced-50-drain
           a1 i result0))
         (result2
          (verina-advanced-50-drain
           a2 j result1)))
    result2))

;; Removing one matching occurrence at each step gives exact finite-list
;; multiset equality, including multiplicities, and hence List.isPerm.

(defun verina-advanced-50-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (verina-advanced-50-remove-first
          value
          (cdr xs))))
    nil))

(defun verina-advanced-50-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-advanced-50-permutation-p
        (cdr left)
        (verina-advanced-50-remove-first
         (car left)
         right)))
    (equal right nil)))

(defun verina-advanced-50-merge-sorted-postcond
    (a1 a2 result)
  (and
   (verina-advanced-50-nat-listp a1)
   (verina-advanced-50-nat-listp a2)
   (verina-advanced-50-nat-listp result)
   (verina-advanced-50-pairwise-nondecreasing-p result)
   (verina-advanced-50-permutation-p
    result
    (append a1 a2))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent is the complete source precondition over the two Array Nat
;; inputs, and its conclusion applies the complete postcondition to the exact
;; executable mergeSorted result.

(defun
    verina-advanced-50-merge-sorted-spec-satisfied-statement
    (a1 a2)
  (implies
   (verina-advanced-50-merge-sorted-precond
    a1
    a2)
   (verina-advanced-50-merge-sorted-postcond
    a1
    a2
    (verina-advanced-50-merge-sorted
     a1
     a2))))

(value-triple :itpeval-statement-checked)
:q
