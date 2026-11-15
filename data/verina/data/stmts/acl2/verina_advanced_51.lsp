;; Statement-only formalization of VERINA corpus artifact verina_advanced_51,
;; "mergeSorted": the recursive merge of two nondecreasing integer lists is
;; nondecreasing and is a permutation of their concatenation. This file
;; contains no proof.

(in-package "ACL2")

(defun verina-advanced-51-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-51-integer-listp (cdr xs)))
    (equal xs nil)))

;; Lean's List.Pairwise (fun x y => x <= y) requires each head to be at most
;; every later element, recursively.

(defun verina-advanced-51-head-at-most-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= x (car xs))
       (verina-advanced-51-head-at-most-all-p
        x
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-51-pairwise-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-51-head-at-most-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-51-pairwise-nondecreasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-51-merge-sorted-precond (a b)
  (and
   (verina-advanced-51-pairwise-nondecreasing-p a)
   (verina-advanced-51-pairwise-nondecreasing-p b)))

;; This recursion is exactly mergeSortedAux. When both lists are nonempty it
;; emits the left head on equality, just as the source's x <= y branch does.

(defun verina-advanced-51-merge-sorted-aux (xs ys)
  (declare
   (xargs
    :measure
    (+ (acl2-count xs) (acl2-count ys))))
  (if (endp xs)
      ys
    (if (endp ys)
        xs
      (let ((x (car xs))
            (y (car ys)))
        (if (<= x y)
            (cons
             x
             (verina-advanced-51-merge-sorted-aux
              (cdr xs)
              ys))
          (cons
           y
           (verina-advanced-51-merge-sorted-aux
            xs
            (cdr ys))))))))

;; The source wrapper only binds the helper result. Its proof-valued
;; precondition argument has no computational effect and is erased here.

(defun verina-advanced-51-merge-sorted (a b)
  (verina-advanced-51-merge-sorted-aux a b))

;; Removing one matching occurrence at each step gives exact finite-list
;; multiset equality, including multiplicities, and hence List.isPerm.

(defun verina-advanced-51-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (verina-advanced-51-remove-first
          value
          (cdr xs))))
    nil))

(defun verina-advanced-51-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-advanced-51-permutation-p
        (cdr left)
        (verina-advanced-51-remove-first
         (car left)
         right)))
    (equal right nil)))

(defun verina-advanced-51-merge-sorted-postcond
    (a b result)
  (and
   (verina-advanced-51-integer-listp a)
   (verina-advanced-51-integer-listp b)
   (verina-advanced-51-integer-listp result)
   (verina-advanced-51-pairwise-nondecreasing-p result)
   (verina-advanced-51-permutation-p
    result
    (append a b))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves both List Int binders and the source precondition,
;; while its conclusion applies the complete postcondition to the exact
;; executable result.

(defun
    verina-advanced-51-merge-sorted-spec-satisfied-statement
    (a b)
  (implies
   (and
    (verina-advanced-51-integer-listp a)
    (verina-advanced-51-integer-listp b)
    (verina-advanced-51-merge-sorted-precond a b))
   (verina-advanced-51-merge-sorted-postcond
    a
    b
    (verina-advanced-51-merge-sorted a b))))

(value-triple :itpeval-statement-checked)
:q
