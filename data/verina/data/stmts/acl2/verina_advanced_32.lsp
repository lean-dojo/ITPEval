;; Statement-only formalization of VERINA corpus artifact verina_advanced_32,
;; "longestIncreasingSubsequence": a deterministic dynamic-programming scan
;; computes the length of a longest strictly increasing subsequence of an
;; integer list, together with its exhaustive subsequence contract. This file
;; contains no proof.

(in-package "ACL2")

(defun verina-advanced-32-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-32-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The List Int binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-32-longest-increasing-subsequence-precond
    (numbers)
  (declare (ignore numbers))
  t)

(defun verina-advanced-32-nat-max (left right)
  (if (< left right)
      right
    left))

;; This helper is the source findLengthEndingAtCurr recursion. It traverses the
;; previous values and their dynamic-programming lengths in lockstep, stopping
;; if either list ends, and retains the largest length whose value is smaller
;; than the current value.

(defun verina-advanced-32-find-length-ending-at-current
    (previous-values previous-lengths current-value best)
  (declare
   (xargs
    :measure
    (+ (acl2-count previous-values)
       (acl2-count previous-lengths))))
  (if (and
       (consp previous-values)
       (consp previous-lengths))
      (let ((previous-value (car previous-values))
            (previous-length (car previous-lengths)))
        (verina-advanced-32-find-length-ending-at-current
         (cdr previous-values)
         (cdr previous-lengths)
         current-value
         (if (< previous-value current-value)
             (verina-advanced-32-nat-max
              best
              previous-length)
           best)))
    best))

;; Exact recursive translation of the source findMaxLength helper.

(defun verina-advanced-32-find-max-length (lengths)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (let ((maximum-rest
             (verina-advanced-32-find-max-length
              (cdr lengths))))
        (if (> (car lengths) maximum-rest)
            (car lengths)
          maximum-rest))
    0))

;; This is the source buildTables recursion. PREVIOUS-VALUES and
;; PREVIOUS-LENGTHS are extended at the tail exactly as in the Lean program.
;; INDEX is retained and incremented even though the source does not otherwise
;; inspect it.

(defun verina-advanced-32-build-tables
    (remaining previous-values previous-lengths index)
  (declare
   (irrelevant index)
   (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((current-value (car remaining))
             (best-previous-length
              (verina-advanced-32-find-length-ending-at-current
               previous-values
               previous-lengths
               current-value
               0))
             (current-length (+ best-previous-length 1)))
        (verina-advanced-32-build-tables
         (cdr remaining)
         (append previous-values (list current-value))
         (append previous-lengths (list current-length))
         (+ index 1)))
    (verina-advanced-32-find-max-length previous-lengths)))

;; The proof-valued True precondition argument is computationally irrelevant.
;; These three branches reproduce the source match on [], [x], and
;; first :: rest.

(defun verina-advanced-32-longest-increasing-subsequence
    (numbers)
  (if (consp numbers)
      (if (consp (cdr numbers))
          (verina-advanced-32-build-tables
           (cdr numbers)
           (list (car numbers))
           (list 1)
           1)
        1)
    0))

;; The following fold, prepend-map, and final reversal reproduce the
;; postcondition's local allSubseq expression, including order and
;; multiplicity.

(defun verina-advanced-32-prepend-to-each
    (value subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons value (car subsequences))
       (verina-advanced-32-prepend-to-each
        value
        (cdr subsequences)))
    nil))

(defun verina-advanced-32-all-subseq-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-32-all-subseq-fold
       (cdr remaining)
       (append
        accumulator
        (verina-advanced-32-prepend-to-each
         (car remaining)
         accumulator)))
    accumulator))

(defun verina-advanced-32-reverse-each
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-32-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-32-all-subseq (numbers)
  (verina-advanced-32-reverse-each
   (verina-advanced-32-all-subseq-fold
    numbers
    (list nil))))

;; Exact Boolean translation of List.Pairwise (fun left right => left < right).

(defun verina-advanced-32-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (< (car xs) (car (cdr xs)))
       (verina-advanced-32-strictly-increasing-p
        (cdr xs)))
    t))

(defun verina-advanced-32-filter-increasing
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (if (verina-advanced-32-strictly-increasing-p
           (car subsequences))
          (cons
           (car subsequences)
           (verina-advanced-32-filter-increasing
            (cdr subsequences)))
        (verina-advanced-32-filter-increasing
         (cdr subsequences)))
    nil))

(defun verina-advanced-32-map-lengths
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (len (car subsequences))
       (verina-advanced-32-map-lengths
        (cdr subsequences)))
    nil))

(defun verina-advanced-32-contains-length-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (or
       (equal (car lengths) result)
       (verina-advanced-32-contains-length-p
        (cdr lengths)
        result))
    nil))

(defun verina-advanced-32-all-lengths-at-most-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-32-all-lengths-at-most-p
        (cdr lengths)
        result))
    t))

(defun verina-advanced-32-longest-increasing-subsequence-postcond
    (numbers result)
  (let* ((all-subseq
          (verina-advanced-32-all-subseq numbers))
         (increasing-subseq
          (verina-advanced-32-filter-increasing
           all-subseq))
         (increasing-subseq-lengths
          (verina-advanced-32-map-lengths
           increasing-subseq)))
    (and
     (verina-advanced-32-integer-listp numbers)
     (natp result)
     (verina-advanced-32-contains-length-p
      increasing-subseq-lengths
      result)
     (verina-advanced-32-all-lengths-at-most-p
      increasing-subseq-lengths
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int binder and True precondition, while its
;; conclusion applies the full postcondition to the executable result.

(defun
    verina-advanced-32-longest-increasing-subsequence-spec-satisfied-statement
    (numbers)
  (implies
   (and
    (verina-advanced-32-integer-listp numbers)
    (verina-advanced-32-longest-increasing-subsequence-precond
     numbers))
   (verina-advanced-32-longest-increasing-subsequence-postcond
    numbers
    (verina-advanced-32-longest-increasing-subsequence
     numbers))))

(value-triple :itpeval-statement-checked)
:q
