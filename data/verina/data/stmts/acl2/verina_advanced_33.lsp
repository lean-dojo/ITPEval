;; Statement-only formalization of VERINA corpus artifact verina_advanced_33,
;; "longestIncreasingSubsequence": a deterministic take-or-skip recursion
;; computes the length of a longest strictly increasing subsequence of an
;; integer list, together with its exhaustive subsequence contract. This file
;; contains no proof.

(in-package "ACL2")

(defun verina-advanced-33-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-33-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The List Int binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-33-longest-increasing-subsequence-precond
    (nums)
  (declare (ignore nums))
  t)

;; This is the source max2 helper, including its choice of the right argument
;; when the two natural numbers are equal.

(defun verina-advanced-33-nat-max2 (left right)
  (if (> left right)
      left
    right))

;; The local listLength helper is retained exactly even though the source
;; implementation does not call it.

(defun verina-advanced-33-list-length (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (+ 1
         (verina-advanced-33-list-length
          (cdr xs)))
    0))

;; A Lean Option Int is represented by NIL for none and the dotted pair
;; (:SOME . value) for some value. This is a bijective representation of the
;; typed source domain.

(defun verina-advanced-33-int-option-p (previous)
  (or
   (equal previous nil)
   (and
    (consp previous)
    (equal (car previous) :some)
    (integerp (cdr previous)))))

(defun verina-advanced-33-some-int (value)
  (cons :some value))

(defun verina-advanced-33-option-get-default (previous)
  (if (and
       (consp previous)
       (equal (car previous) :some)
       (integerp (cdr previous)))
      (cdr previous)
    0))

;; Exact recursive translation of the source helper. At each element it
;; compares the branch that takes the element, when permitted by PREVIOUS,
;; with the branch that skips it.

(defun verina-advanced-33-helper (lst previous)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (let* ((head (car lst))
             (tail (cdr lst))
             (can-take
              (if (equal previous nil)
                  t
                (if (<
                     (verina-advanced-33-option-get-default
                      previous)
                     head)
                    t
                  nil)))
             (with-take
              (if can-take
                  (+ 1
                     (verina-advanced-33-helper
                      tail
                      (verina-advanced-33-some-int
                       head)))
                0))
             (without-take
              (verina-advanced-33-helper
               tail
               previous)))
        (verina-advanced-33-nat-max2
         with-take
         without-take))
    0))

;; The proof-valued True precondition argument is computationally irrelevant.
;; The executable function is exactly the source call helper nums none.

(defun verina-advanced-33-longest-increasing-subsequence
    (nums)
  (verina-advanced-33-helper nums nil))

;; The following fold, prepend-map, and final reversal reproduce the
;; postcondition's local allSubseq expression, including order and
;; multiplicity.

(defun verina-advanced-33-prepend-to-each
    (value subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons value (car subsequences))
       (verina-advanced-33-prepend-to-each
        value
        (cdr subsequences)))
    nil))

(defun verina-advanced-33-all-subseq-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-33-all-subseq-fold
       (cdr remaining)
       (append
        accumulator
        (verina-advanced-33-prepend-to-each
         (car remaining)
         accumulator)))
    accumulator))

(defun verina-advanced-33-reverse-each
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-33-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-33-all-subseq (nums)
  (verina-advanced-33-reverse-each
   (verina-advanced-33-all-subseq-fold
    nums
    (list nil))))

;; These two predicates exactly represent List.Pairwise (fun x y => x < y):
;; every head is less than every later element, recursively.

(defun verina-advanced-33-head-less-than-all-p
    (head tail)
  (declare (xargs :measure (acl2-count tail)))
  (if (consp tail)
      (and
       (< head (car tail))
       (verina-advanced-33-head-less-than-all-p
        head
        (cdr tail)))
    (equal tail nil)))

(defun verina-advanced-33-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-33-head-less-than-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-33-strictly-increasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-33-filter-increasing
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (if (verina-advanced-33-strictly-increasing-p
           (car subsequences))
          (cons
           (car subsequences)
           (verina-advanced-33-filter-increasing
            (cdr subsequences)))
        (verina-advanced-33-filter-increasing
         (cdr subsequences)))
    nil))

(defun verina-advanced-33-map-lengths
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (len (car subsequences))
       (verina-advanced-33-map-lengths
        (cdr subsequences)))
    nil))

(defun verina-advanced-33-contains-length-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (or
       (equal (car lengths) result)
       (verina-advanced-33-contains-length-p
        (cdr lengths)
        result))
    nil))

(defun verina-advanced-33-all-lengths-at-most-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-33-all-lengths-at-most-p
        (cdr lengths)
        result))
    t))

(defun verina-advanced-33-longest-increasing-subsequence-postcond
    (nums result)
  (let* ((all-subseq
          (verina-advanced-33-all-subseq nums))
         (increasing-subseq
          (verina-advanced-33-filter-increasing
           all-subseq))
         (increasing-subseq-lengths
          (verina-advanced-33-map-lengths
           increasing-subseq)))
    (and
     (verina-advanced-33-integer-listp nums)
     (natp result)
     (verina-advanced-33-contains-length-p
      increasing-subseq-lengths
      result)
     (verina-advanced-33-all-lengths-at-most-p
      increasing-subseq-lengths
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition, while its
;; conclusion applies the full postcondition to the executable result.

(defun
    verina-advanced-33-longest-increasing-subsequence-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-33-integer-listp nums)
    (verina-advanced-33-longest-increasing-subsequence-precond
     nums))
   (verina-advanced-33-longest-increasing-subsequence-postcond
    nums
    (verina-advanced-33-longest-increasing-subsequence
     nums))))

(value-triple :itpeval-statement-checked)
:q
