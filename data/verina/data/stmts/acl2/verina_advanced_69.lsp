;; Statement-only formalization of VERINA corpus artifact verina_advanced_69,
;; "searchInsert": a left-to-right search of a strictly increasing integer
;; list returns the target's index or its sorted insertion index, together
;; with the corresponding finite-index correctness contract. This file
;; contains no proof.

(in-package "ACL2")

(defun verina-advanced-69-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-69-integer-listp (cdr xs)))
    (equal xs nil)))

;; Lean's List.Pairwise (fun x y => x < y) relates each head to every later
;; element, then recursively imposes the same condition on the tail.

(defun verina-advanced-69-head-less-than-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (< x (car xs))
       (verina-advanced-69-head-less-than-all-p
        x
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-69-pairwise-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-69-head-less-than-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-69-pairwise-strictly-increasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-69-search-insert-precond (xs target)
  (declare (ignore target))
  (verina-advanced-69-pairwise-strictly-increasing-p xs))

;; This is the source local helper: inspect elements from left to right,
;; returning the current natural index at the first y with target <= y.

(defun verina-advanced-69-search-insert-helper
    (ys idx target)
  (declare (xargs :measure (acl2-count ys)))
  (if (consp ys)
      (if (<= target (car ys))
          idx
        (verina-advanced-69-search-insert-helper
         (cdr ys)
         (+ idx 1)
         target))
    idx))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. The empty branch and nonempty helper call preserve
;; the source program exactly.

(defun verina-advanced-69-search-insert (xs target)
  (if (consp xs)
      (verina-advanced-69-search-insert-helper xs 0 target)
    0))

;; List.get! on List Int returns the default integer 0 out of bounds.

(defun verina-advanced-69-nth-default-zero (index xs)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp xs)
        (if (zp index)
            (car xs)
          (verina-advanced-69-nth-default-zero
           (- index 1)
           (cdr xs)))
      0)))

;; This recursion is List.range RESULT followed by List.all of
;; (fun i => xs[i]! < target), including get!'s default behavior.

(defun verina-advanced-69-all-before-less-p
    (remaining xs target)
  (declare (xargs :measure (nfix remaining)))
  (if (not (natp remaining))
      nil
    (if (zp remaining)
        t
      (and
       (<
        (verina-advanced-69-nth-default-zero 0 xs)
        target)
       (verina-advanced-69-all-before-less-p
        (- remaining 1)
        (if (consp xs) (cdr xs) nil)
        target)))))

(defun verina-advanced-69-search-insert-postcond
    (xs target result)
  (and
   (verina-advanced-69-integer-listp xs)
   (integerp target)
   (natp result)
   (<= result (len xs))
   (verina-advanced-69-all-before-less-p
    result
    xs
    target)
   (implies
    (< result (len xs))
    (<=
     target
     (verina-advanced-69-nth-default-zero result xs)))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int and Int binders and the complete source
;; precondition; its conclusion applies the complete postcondition to the
;; exact executable result.

(defun
    verina-advanced-69-search-insert-spec-satisfied-statement
    (xs target)
  (implies
   (and
    (verina-advanced-69-integer-listp xs)
    (integerp target)
    (verina-advanced-69-search-insert-precond xs target))
   (verina-advanced-69-search-insert-postcond
    xs
    target
    (verina-advanced-69-search-insert xs target))))

(value-triple :itpeval-statement-checked)
:q
