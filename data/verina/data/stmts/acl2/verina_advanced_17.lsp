;; Statement-only formalization of VERINA corpus artifact verina_advanced_17,
;; "insertionSort": recursive insertion sort returns a nondecreasing integer
;; list that is a permutation of its input. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-17-integer-listp (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-17-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True; the List Int input domain is explicit in
;; the final correctness statement.

(defun verina-advanced-17-insertion-sort-precond (xs)
  (declare (ignore xs))
  t)

;; These recursive functions are exactly the source insertElement and sortList
;; helpers. The proof-valued precondition argument to insertionSort is erased.

(defun verina-advanced-17-insert-element (x ys)
  (if (consp ys)
      (let ((y (car ys)))
        (if (<= x y)
            (cons x ys)
          (cons
           y
           (verina-advanced-17-insert-element x (cdr ys)))))
    (list x)))

(defun verina-advanced-17-sort-list (xs)
  (if (consp xs)
      (verina-advanced-17-insert-element
       (car xs)
       (verina-advanced-17-sort-list (cdr xs)))
    nil))

(defun verina-advanced-17-insertion-sort (xs)
  (verina-advanced-17-sort-list xs))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later element and recursively imposes the same condition on the tail.

(defun verina-advanced-17-head-at-most-all-p (x ys)
  (if (consp ys)
      (and
       (<= x (car ys))
       (verina-advanced-17-head-at-most-all-p x (cdr ys)))
    (equal ys nil)))

(defun verina-advanced-17-pairwise-nondecreasing-p (xs)
  (if (consp xs)
      (and
       (verina-advanced-17-head-at-most-all-p
        (car xs) (cdr xs))
       (verina-advanced-17-pairwise-nondecreasing-p
        (cdr xs)))
    (equal xs nil)))

;; Removing one matching occurrence at each step gives exact finite-list
;; multiset equality, including multiplicities, and hence List.isPerm.

(defun verina-advanced-17-remove-first (value xs)
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (verina-advanced-17-remove-first value (cdr xs))))
    nil))

(defun verina-advanced-17-permutation-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-advanced-17-permutation-p
        (cdr left)
        (verina-advanced-17-remove-first (car left) right)))
    (equal right nil)))

(defun verina-advanced-17-insertion-sort-postcond
    (xs result)
  (and
   (verina-advanced-17-integer-listp xs)
   (verina-advanced-17-integer-listp result)
   (verina-advanced-17-pairwise-nondecreasing-p result)
   (verina-advanced-17-permutation-p xs result)))

(defun
    verina-advanced-17-insertion-sort-spec-satisfied-statement
    (xs)
  (implies
   (and
    (verina-advanced-17-integer-listp xs)
    (verina-advanced-17-insertion-sort-precond xs))
   (verina-advanced-17-insertion-sort-postcond
    xs
    (verina-advanced-17-insertion-sort xs))))

(value-triple :itpeval-statement-checked)
:q
