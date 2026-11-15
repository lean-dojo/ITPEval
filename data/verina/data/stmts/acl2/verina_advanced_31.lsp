;; Statement-only formalization of VERINA corpus artifact verina_advanced_31,
;; "longestIncreasingSubseqLength": a deterministic exhaustive subsequence
;; computation returns the maximum length of a strictly increasing subsequence
;; of an integer list. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-31-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-31-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The List Int binder domain is explicit in
;; the final correctness statement.

(defun
    verina-advanced-31-longest-increasing-subseq-length-precond
    (xs)
  (declare (ignore xs))
  t)

(defun verina-advanced-31-prepend-to-each
    (x subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons x (car subsequences))
       (verina-advanced-31-prepend-to-each
        x
        (cdr subsequences)))
    nil))

;; This is the source subsequences recursion, including its order and
;; multiplicity: first all subsequences omitting the head, then the same list
;; with the head prepended to every member.

(defun verina-advanced-31-subsequences (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (let ((subs
             (verina-advanced-31-subsequences
              (cdr xs))))
        (append
         subs
         (verina-advanced-31-prepend-to-each
          (car xs)
          subs)))
    (list nil)))

;; Exact Boolean translation of the source isStrictlyIncreasing recursion.

(defun verina-advanced-31-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (< (car xs) (car (cdr xs)))
       (verina-advanced-31-strictly-increasing-p
        (cdr xs)))
    t))

(defun verina-advanced-31-filter-increasing
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (if (verina-advanced-31-strictly-increasing-p
           (car subsequences))
          (cons
           (car subsequences)
           (verina-advanced-31-filter-increasing
            (cdr subsequences)))
        (verina-advanced-31-filter-increasing
         (cdr subsequences)))
    nil))

(defun verina-advanced-31-nat-max (left right)
  (if (< left right)
      right
    left))

;; This left fold starts at zero and updates with max(acc, length(s)), exactly
;; reproducing the source executable implementation after filtering.

(defun verina-advanced-31-fold-max-length
    (subsequences accumulator)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (verina-advanced-31-fold-max-length
       (cdr subsequences)
       (verina-advanced-31-nat-max
        accumulator
        (len (car subsequences))))
    accumulator))

;; The proof-valued True precondition argument is computationally irrelevant.

(defun
    verina-advanced-31-longest-increasing-subseq-length
    (xs)
  (let* ((subs
          (verina-advanced-31-subsequences xs))
         (increasing
          (verina-advanced-31-filter-increasing
           subs)))
    (verina-advanced-31-fold-max-length
     increasing
     0)))

;; The following fold, prepend-map, and final reversal separately reproduce
;; the postcondition's local allSubseq expression.

(defun verina-advanced-31-all-subseq-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-31-all-subseq-fold
       (cdr remaining)
       (append
        accumulator
        (verina-advanced-31-prepend-to-each
         (car remaining)
         accumulator)))
    accumulator))

(defun verina-advanced-31-reverse-each
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-31-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-31-all-subseq (xs)
  (verina-advanced-31-reverse-each
   (verina-advanced-31-all-subseq-fold
    xs
    (list nil))))

(defun verina-advanced-31-map-lengths
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (len (car subsequences))
       (verina-advanced-31-map-lengths
        (cdr subsequences)))
    nil))

(defun verina-advanced-31-contains-length-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (or
       (equal (car lengths) result)
       (verina-advanced-31-contains-length-p
        (cdr lengths)
        result))
    nil))

(defun verina-advanced-31-all-lengths-at-most-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-31-all-lengths-at-most-p
        (cdr lengths)
        result))
    t))

(defun
    verina-advanced-31-longest-increasing-subseq-length-postcond
    (xs result)
  (let* ((all-subseq
          (verina-advanced-31-all-subseq xs))
         (increasing-subseq
          (verina-advanced-31-filter-increasing
           all-subseq))
         (increasing-subseq-lens
          (verina-advanced-31-map-lengths
           increasing-subseq)))
    (and
     (verina-advanced-31-integer-listp xs)
     (natp result)
     (verina-advanced-31-contains-length-p
      increasing-subseq-lens
      result)
     (verina-advanced-31-all-lengths-at-most-p
      increasing-subseq-lens
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition, while its
;; conclusion applies the full postcondition to the executable result.

(defun
    verina-advanced-31-longest-increasing-subseq-length-spec-satisfied-statement
    (xs)
  (implies
   (and
    (verina-advanced-31-integer-listp xs)
    (verina-advanced-31-longest-increasing-subseq-length-precond
     xs))
   (verina-advanced-31-longest-increasing-subseq-length-postcond
    xs
    (verina-advanced-31-longest-increasing-subseq-length
     xs))))

(value-triple :itpeval-statement-checked)
:q
