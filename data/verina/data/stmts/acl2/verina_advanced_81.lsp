;; Statement-only formalization of VERINA corpus artifact verina_advanced_81,
;; catalog title "uniqueSorted": deterministic duplicate removal followed by
;; insertion sort returns a permutation of the duplicate-erased integer input
;; in nondecreasing order. This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-81-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-81-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True; the List Int domain remains explicit in
;; the final correctness proposition.

(defun verina-advanced-81-unique-sorted-precond (arr)
  (declare (ignore arr))
  t)

;; These definitions reproduce the source-local insert and insertionSort
;; recursions after erasing the proof-valued precondition argument.

(defun verina-advanced-81-insert (x sorted)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (let ((head (car sorted)))
        (if (<= x head)
            (cons x sorted)
          (cons
           head
           (verina-advanced-81-insert x (cdr sorted)))))
    (list x)))

(defun verina-advanced-81-insertion-sort (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (verina-advanced-81-insert
       (car xs)
       (verina-advanced-81-insertion-sort (cdr xs)))
    nil))

;; This is the source-local removeDups auxiliary: SEEN stores prior values in
;; reverse order, ACC stores the first occurrences in reverse order, and the
;; final reverse restores their input order.

(defun verina-advanced-81-remove-dups-aux
    (remaining seen acc)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (member-equal (car remaining) seen)
          (verina-advanced-81-remove-dups-aux
           (cdr remaining)
           seen
           acc)
        (verina-advanced-81-remove-dups-aux
         (cdr remaining)
         (cons (car remaining) seen)
         (cons (car remaining) acc)))
    (reverse acc)))

(defun verina-advanced-81-remove-dups (xs)
  (verina-advanced-81-remove-dups-aux xs nil nil))

(defun verina-advanced-81-unique-sorted (arr)
  (verina-advanced-81-insertion-sort
   (verina-advanced-81-remove-dups arr)))

;; Lean's List.eraseDups keeps the first occurrence of each integer. This
;; separate definition represents the library operation used by the source
;; postcondition.

(defun verina-advanced-81-erase-dups-aux
    (remaining seen-reversed)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (member-equal (car remaining) seen-reversed)
          (verina-advanced-81-erase-dups-aux
           (cdr remaining)
           seen-reversed)
        (verina-advanced-81-erase-dups-aux
         (cdr remaining)
         (cons (car remaining) seen-reversed)))
    (reverse seen-reversed)))

(defun verina-advanced-81-erase-dups (xs)
  (verina-advanced-81-erase-dups-aux xs nil))

;; Removing one matching occurrence at every recursive step characterizes
;; List.isPerm, including multiplicities.

(defun verina-advanced-81-remove-first (value xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (equal value (car xs))
          (cdr xs)
        (cons
         (car xs)
         (verina-advanced-81-remove-first
          value
          (cdr xs))))
    nil))

(defun verina-advanced-81-permutation-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-advanced-81-permutation-p
        (cdr left)
        (verina-advanced-81-remove-first
         (car left)
         right)))
    (equal right nil)))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later element, recursively.

(defun verina-advanced-81-head-at-most-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= x (car xs))
       (verina-advanced-81-head-at-most-all-p
        x
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-81-pairwise-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-81-head-at-most-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-81-pairwise-nondecreasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-81-unique-sorted-postcond
    (arr result)
  (and
   (verina-advanced-81-integer-listp arr)
   (verina-advanced-81-integer-listp result)
   (verina-advanced-81-permutation-p
    (verina-advanced-81-erase-dups arr)
    result)
   (verina-advanced-81-pairwise-nondecreasing-p
    result)))

;; This predicate is the unproved final correctness proposition connecting
;; the complete postcondition to the exact executable result.

(defun
    verina-advanced-81-unique-sorted-spec-satisfied-statement
    (arr)
  (implies
   (and
    (verina-advanced-81-integer-listp arr)
    (verina-advanced-81-unique-sorted-precond arr))
   (verina-advanced-81-unique-sorted-postcond
    arr
    (verina-advanced-81-unique-sorted arr))))

(value-triple :itpeval-statement-checked)
:q
