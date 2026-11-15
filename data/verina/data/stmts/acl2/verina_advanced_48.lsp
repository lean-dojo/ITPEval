;; Statement-only formalization of VERINA corpus artifact verina_advanced_48,
;; "mergeSort": the executable insertion-sort implementation returns a
;; nondecreasing integer list that is a permutation of its input. This file
;; contains no proof.

(in-package "ACL2")

(defun verina-advanced-48-integer-listp (list)
  (if (consp list)
      (and
       (integerp (car list))
       (verina-advanced-48-integer-listp (cdr list)))
    (equal list nil)))

;; The source precondition is True; the List Int input domain is explicit in
;; the final correctness statement.

(defun verina-advanced-48-merge-sort-precond (list)
  (declare (ignore list))
  t)

;; These are the source's local insert and sort helpers. In particular, the
;; program named mergeSort computes this insertion sort, exactly as in the
;; primary Lean source. The proof-valued precondition argument is erased.

(defun verina-advanced-48-insert (x sorted)
  (if (consp sorted)
      (let ((y (car sorted)))
        (if (<= x y)
            (cons x sorted)
          (cons
           y
           (verina-advanced-48-insert x (cdr sorted)))))
    (list x)))

(defun verina-advanced-48-sort (list)
  (if (consp list)
      (verina-advanced-48-insert
       (car list)
       (verina-advanced-48-sort (cdr list)))
    nil))

(defun verina-advanced-48-merge-sort (list)
  (verina-advanced-48-sort list))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later element and recursively imposes the same condition on the tail.

(defun verina-advanced-48-head-at-most-all-p (x list)
  (if (consp list)
      (and
       (<= x (car list))
       (verina-advanced-48-head-at-most-all-p x (cdr list)))
    (equal list nil)))

(defun verina-advanced-48-pairwise-nondecreasing-p (list)
  (if (consp list)
      (and
       (verina-advanced-48-head-at-most-all-p
        (car list) (cdr list))
       (verina-advanced-48-pairwise-nondecreasing-p
        (cdr list)))
    (equal list nil)))

;; Removing one matching occurrence at each step gives exact finite-list
;; multiset equality, including multiplicities, and hence List.isPerm.

(defun verina-advanced-48-remove-first (value list)
  (if (consp list)
      (if (equal value (car list))
          (cdr list)
        (cons
         (car list)
         (verina-advanced-48-remove-first value (cdr list))))
    nil))

(defun verina-advanced-48-permutation-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-advanced-48-permutation-p
        (cdr left)
        (verina-advanced-48-remove-first (car left) right)))
    (equal right nil)))

(defun verina-advanced-48-merge-sort-postcond
    (list result)
  (and
   (verina-advanced-48-integer-listp list)
   (verina-advanced-48-integer-listp result)
   (verina-advanced-48-pairwise-nondecreasing-p result)
   (verina-advanced-48-permutation-p list result)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition; its
;; conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-48-merge-sort-spec-satisfied-statement
    (list)
  (implies
   (and
    (verina-advanced-48-integer-listp list)
    (verina-advanced-48-merge-sort-precond list))
   (verina-advanced-48-merge-sort-postcond
    list
    (verina-advanced-48-merge-sort list))))

(value-triple :itpeval-statement-checked)
:q
