;; Statement-only formalization of VERINA corpus artifact verina_advanced_4,
;; "LongestIncreasingSubsequence": a deterministic array dynamic program
;; returns the length of a longest strictly increasing subsequence, with its
;; exhaustive subsequence correctness contract. This file contains no proof.

(in-package "ACL2")

;; A Lean Array Int is represented canonically by a proper ACL2 list of
;; integers.

(defun verina-advanced-4-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-4-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The Array Int binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-4-longest-increasing-subsequence-precond
    (a)
  (declare (ignore a))
  t)

;; Exact translation of the source helper on integers.

(defun verina-advanced-4-int-max (x y)
  (if (< x y)
      y
    x))

;; Array.mkArray n 1 is represented by a proper list of n integer ones.

(defun verina-advanced-4-make-ones (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     1
     (verina-advanced-4-make-ones
      (- count 1)))))

;; Array.get! on Array Int returns zero outside the array. All reads reached by
;; the source loops are in bounds, while this definition also preserves the
;; source operation's total default behavior.

(defun verina-advanced-4-array-read (index array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp array)
        (if (zp index)
            (car array)
          (verina-advanced-4-array-read
           (- index 1)
           (cdr array)))
      0)))

;; Array.set! at a valid index replaces exactly that entry. The reachable
;; source indices are valid; out-of-bounds indices leave the array unchanged.

(defun verina-advanced-4-array-set
    (index value array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      array
    (if (consp array)
        (if (zp index)
            (cons value (cdr array))
          (cons
           (car array)
           (verina-advanced-4-array-set
            (- index 1)
            value
            (cdr array))))
      nil)))

;; This is one complete source inner loop, processing j = 0,...,i-1 in order.
;; The mutable DP state is updated immediately after each successful
;; comparison, exactly as in the Id.run computation.

(defun verina-advanced-4-dp-inner-loop
    (a i j remaining dp)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      dp
    (let* ((a-j
            (verina-advanced-4-array-read j a))
           (a-i
            (verina-advanced-4-array-read i a))
           (next-dp
            (if (< a-j a-i)
                (let* ((dp-i
                        (verina-advanced-4-array-read i dp))
                       (dp-j
                        (verina-advanced-4-array-read j dp))
                       (new-value
                        (verina-advanced-4-int-max
                         dp-i
                         (+ dp-j 1))))
                  (verina-advanced-4-array-set
                   i
                   new-value
                   dp))
              dp)))
      (verina-advanced-4-dp-inner-loop
       a
       i
       (+ j 1)
       (- remaining 1)
       next-dp))))

;; This is the source outer loop i = 1,...,n-1. At each index, the inner loop
;; consumes the already established prefix of DP entries.

(defun verina-advanced-4-dp-outer-loop
    (a i remaining dp)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      dp
    (let ((next-dp
           (verina-advanced-4-dp-inner-loop
            a
            i
            0
            i
            dp)))
      (verina-advanced-4-dp-outer-loop
       a
       (+ i 1)
       (- remaining 1)
       next-dp))))

;; Exact left fold of intMax with initial value zero.

(defun verina-advanced-4-fold-int-max
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-4-fold-int-max
       (cdr remaining)
       (verina-advanced-4-int-max
        accumulator
        (car remaining)))
    accumulator))

;; The proof-valued True precondition argument is computationally irrelevant.
;; These bindings reproduce Array.mkArray, both sequential ranges, the empty
;; array match, and the final fold of the source implementation.

(defun verina-advanced-4-longest-increasing-subsequence
    (a)
  (let* ((n (len a))
         (initial-dp
          (verina-advanced-4-make-ones n))
         (final-dp
          (verina-advanced-4-dp-outer-loop
           a
           1
           (nfix (- n 1))
           initial-dp)))
    (if (endp final-dp)
        0
      (verina-advanced-4-fold-int-max
       final-dp
       0))))

;; The next definitions reproduce the postcondition's local allSubseq. At
;; each input element, the accumulator is followed by a mapped copy with that
;; element prepended; every final subsequence is then reversed.

(defun verina-advanced-4-prepend-to-each
    (value subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons value (car subsequences))
       (verina-advanced-4-prepend-to-each
        value
        (cdr subsequences)))
    nil))

(defun verina-advanced-4-all-subseq-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-4-all-subseq-fold
       (cdr remaining)
       (append
        accumulator
        (verina-advanced-4-prepend-to-each
         (car remaining)
         accumulator)))
    accumulator))

(defun verina-advanced-4-reverse-each
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-4-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-4-all-subseq (a)
  (verina-advanced-4-reverse-each
   (verina-advanced-4-all-subseq-fold
    a
    (list nil))))

;; These predicates are a direct Boolean rendering of List.Pairwise (<):
;; every head is less than every later element, recursively.

(defun verina-advanced-4-head-less-than-all-p
    (head tail)
  (declare (xargs :measure (acl2-count tail)))
  (if (consp tail)
      (and
       (< head (car tail))
       (verina-advanced-4-head-less-than-all-p
        head
        (cdr tail)))
    (equal tail nil)))

(defun verina-advanced-4-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-advanced-4-head-less-than-all-p
        (car xs)
        (cdr xs))
       (verina-advanced-4-strictly-increasing-p
        (cdr xs)))
    (equal xs nil)))

(defun verina-advanced-4-filter-increasing
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (if (verina-advanced-4-strictly-increasing-p
           (car subsequences))
          (cons
           (car subsequences)
           (verina-advanced-4-filter-increasing
            (cdr subsequences)))
        (verina-advanced-4-filter-increasing
         (cdr subsequences)))
    nil))

(defun verina-advanced-4-map-lengths
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (len (car subsequences))
       (verina-advanced-4-map-lengths
        (cdr subsequences)))
    nil))

(defun verina-advanced-4-contains-length-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (or
       (equal (car lengths) result)
       (verina-advanced-4-contains-length-p
        (cdr lengths)
        result))
    nil))

(defun verina-advanced-4-all-lengths-at-most-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-4-all-lengths-at-most-p
        (cdr lengths)
        result))
    t))

(defun
    verina-advanced-4-longest-increasing-subsequence-postcond
    (a result)
  (let* ((all-subseq
          (verina-advanced-4-all-subseq a))
         (increasing-subseq
          (verina-advanced-4-filter-increasing
           all-subseq))
         (increasing-subseq-lengths
          (verina-advanced-4-map-lengths
           increasing-subseq)))
    (and
     (verina-advanced-4-integer-listp a)
     (integerp result)
     (verina-advanced-4-contains-length-p
      increasing-subseq-lengths
      result)
     (verina-advanced-4-all-lengths-at-most-p
      increasing-subseq-lengths
      result))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the Array Int binder and True precondition, while its
;; conclusion applies the complete postcondition to the executable result.

(defun
    verina-advanced-4-longest-increasing-subsequence-spec-satisfied-statement
    (a)
  (implies
   (and
    (verina-advanced-4-integer-listp a)
    (verina-advanced-4-longest-increasing-subsequence-precond
     a))
   (verina-advanced-4-longest-increasing-subsequence-postcond
    a
    (verina-advanced-4-longest-increasing-subsequence
     a))))

(value-triple :itpeval-statement-checked)
:q
