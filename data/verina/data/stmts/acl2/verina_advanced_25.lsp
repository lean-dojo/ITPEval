;; Statement-only formalization of VERINA corpus artifact verina_advanced_25,
;; "lengthOfLIS": a deterministic dynamic-programming computation returns the
;; length of a longest strictly increasing subsequence, together with its
;; exhaustive subsequence correctness contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-25-integer-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-25-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True. The List Int input domain is made explicit
;; in the final correctness statement.

(defun verina-advanced-25-length-of-lis-precond (nums)
  (declare (ignore nums))
  t)

;; Array.mkArray n 1 is represented by a proper list of n natural-number ones.

(defun verina-advanced-25-make-ones (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     1
     (verina-advanced-25-make-ones
      (- count 1)))))

;; This is one complete source inner loop. J is its current index and
;; REMAINING is the number of indices still to process. UPDATE-NTH is exact
;; here because every reachable I is within the fixed-length DP list.

(defun verina-advanced-25-dp-inner-loop
    (j remaining i nums dp)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      dp
    (let* ((nums-j (nth j nums))
           (nums-i (nth i nums))
           (dp-j (nth j dp))
           (dp-i (nth i dp))
           (next-dp
            (if (and
                 (< nums-j nums-i)
                 (> (+ dp-j 1) dp-i))
                (update-nth i (+ dp-j 1) dp)
              dp)))
      (verina-advanced-25-dp-inner-loop
       (+ j 1)
       (- remaining 1)
       i
       nums
       next-dp))))

;; This is the source outer loop over i = 1,...,n-1. Each inner loop consumes
;; the already computed entries j = 0,...,i-1 in their original order.

(defun verina-advanced-25-dp-outer-loop
    (i remaining nums dp)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      dp
    (let ((next-dp
           (verina-advanced-25-dp-inner-loop
            0 i i nums dp)))
      (verina-advanced-25-dp-outer-loop
       (+ i 1)
       (- remaining 1)
       nums
       next-dp))))

;; Exact left fold used by the source maxInArray helper, with initial value 0.

(defun verina-advanced-25-max-in-array-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((entry (car remaining)))
        (verina-advanced-25-max-in-array-fold
         (cdr remaining)
         (if (>= accumulator entry)
             accumulator
           entry)))
    accumulator))

(defun verina-advanced-25-max-in-array (arr)
  (verina-advanced-25-max-in-array-fold arr 0))

;; The proof-valued precondition argument is computationally irrelevant in the
;; source. On a nonempty input, the following definitions reproduce the
;; Array.mkArray initialization, both sequential for-loops, and final fold.

(defun verina-advanced-25-length-of-lis (nums)
  (if (endp nums)
      0
    (let* ((n (len nums))
           (initial-dp
            (verina-advanced-25-make-ones n))
           (final-dp
            (verina-advanced-25-dp-outer-loop
             1
             (- n 1)
             nums
             initial-dp)))
      (verina-advanced-25-max-in-array final-dp))))

;; The next four definitions reproduce the postcondition's fold from [[]].
;; At each input element x, the accumulator is followed by a map that prepends
;; x to every accumulated list; all lists are reversed after the fold.

(defun verina-advanced-25-prepend-to-each
    (x subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons x (car subsequences))
       (verina-advanced-25-prepend-to-each
        x
        (cdr subsequences)))
    nil))

(defun verina-advanced-25-subsequence-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((next-accumulator
             (append
              accumulator
              (verina-advanced-25-prepend-to-each
               (car remaining)
               accumulator))))
        (verina-advanced-25-subsequence-fold
         (cdr remaining)
         next-accumulator))
    accumulator))

(defun verina-advanced-25-reverse-each
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-25-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-25-all-subsequences (nums)
  (verina-advanced-25-reverse-each
   (verina-advanced-25-subsequence-fold
    nums
    (list nil))))

;; Exact Boolean translation of List.Pairwise (fun a b => a < b).

(defun verina-advanced-25-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (< (car xs) (car (cdr xs)))
       (verina-advanced-25-strictly-increasing-p
        (cdr xs)))
    t))

(defun verina-advanced-25-filter-increasing
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (if (verina-advanced-25-strictly-increasing-p
           (car subsequences))
          (cons
           (car subsequences)
           (verina-advanced-25-filter-increasing
            (cdr subsequences)))
        (verina-advanced-25-filter-increasing
         (cdr subsequences)))
    nil))

(defun verina-advanced-25-map-lengths
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (len (car subsequences))
       (verina-advanced-25-map-lengths
        (cdr subsequences)))
    nil))

(defun verina-advanced-25-contains-length-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (or
       (equal (car lengths) result)
       (verina-advanced-25-contains-length-p
        (cdr lengths)
        result))
    nil))

(defun verina-advanced-25-all-lengths-at-most-p
    (lengths result)
  (declare (xargs :measure (acl2-count lengths)))
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-25-all-lengths-at-most-p
        (cdr lengths)
        result))
    t))

(defun verina-advanced-25-length-of-lis-postcond
    (nums result)
  (let* ((all-subsequences
          (verina-advanced-25-all-subsequences nums))
         (increasing-subsequences
          (verina-advanced-25-filter-increasing
           all-subsequences))
         (increasing-subsequence-lengths
          (verina-advanced-25-map-lengths
           increasing-subsequences)))
    (and
     (verina-advanced-25-integer-listp nums)
     (natp result)
     (verina-advanced-25-contains-length-p
      increasing-subsequence-lengths
      result)
     (verina-advanced-25-all-lengths-at-most-p
      increasing-subsequence-lengths
      result))))

;; This predicate is the unproved final correctness proposition. The ACL2
;; antecedent expresses the Lean binder type and its True precondition.

(defun
    verina-advanced-25-length-of-lis-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-25-integer-listp nums)
    (verina-advanced-25-length-of-lis-precond nums))
   (verina-advanced-25-length-of-lis-postcond
    nums
    (verina-advanced-25-length-of-lis nums))))

(value-triple :itpeval-statement-checked)
:q
