;; Statement-only formalization of VERINA corpus artifact verina_advanced_24,
;; "lengthOfLIS": a deterministic tail-list fold computes the length of a
;; longest strictly increasing subsequence, together with its exhaustive
;; subsequence correctness contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-24-integer-listp (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-24-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True; the List Int domain is explicit in the
;; final correctness statement.

(defun verina-advanced-24-length-of-lis-precond (nums)
  (declare (ignore nums))
  t)

;; This is the source lisHelper.replace recursion. ACC stores the traversed
;; prefix in reverse order. The first tail value at least x is replaced by x;
;; if no such value exists, x is appended.

(defun verina-advanced-24-replace (remaining accumulator x)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((y (car remaining))
            (ys (cdr remaining)))
        (if (<= x y)
            (append
             (reverse accumulator)
             (cons x ys))
          (verina-advanced-24-replace
           ys
           (cons y accumulator)
           x)))
    (append
     (reverse accumulator)
     (list x))))

(defun verina-advanced-24-lis-helper (dp x)
  (verina-advanced-24-replace dp nil x))

;; Folding left over NUMS exactly reproduces the source finalDP computation.

(defun verina-advanced-24-foldl-lis-helper (remaining dp)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-24-foldl-lis-helper
       (cdr remaining)
       (verina-advanced-24-lis-helper
        dp
        (car remaining)))
    dp))

(defun verina-advanced-24-length-of-lis (nums)
  (len
   (verina-advanced-24-foldl-lis-helper nums nil)))

;; Exact Boolean translation of the postcondition's local
;; isStrictlyIncreasing recursion.

(defun verina-advanced-24-strictly-increasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (and
       (consp xs)
       (consp (cdr xs)))
      (and
       (< (car xs) (car (cdr xs)))
       (verina-advanced-24-strictly-increasing-p
        (cdr xs)))
    t))

(defun verina-advanced-24-prepend-to-each
    (x subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons x (car subsequences))
       (verina-advanced-24-prepend-to-each
        x
        (cdr subsequences)))
    nil))

;; This direct recursion preserves the source order and multiplicity:
;; subsequences xs' followed by the same list with x prepended to each member.

(defun verina-advanced-24-subsequences (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (let ((rest
             (verina-advanced-24-subsequences
              (cdr xs))))
        (append
         rest
         (verina-advanced-24-prepend-to-each
          (car xs)
          rest)))
    (list nil)))

(defun verina-advanced-24-filter-increasing
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (if (verina-advanced-24-strictly-increasing-p
           (car subsequences))
          (cons
           (car subsequences)
           (verina-advanced-24-filter-increasing
            (cdr subsequences)))
        (verina-advanced-24-filter-increasing
         (cdr subsequences)))
    nil))

(defun verina-advanced-24-some-length-equal-p
    (subsequences result)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (or
       (equal (len (car subsequences)) result)
       (verina-advanced-24-some-length-equal-p
        (cdr subsequences)
        result))
    nil))

(defun verina-advanced-24-all-lengths-at-most-p
    (subsequences result)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (and
       (<= (len (car subsequences)) result)
       (verina-advanced-24-all-lengths-at-most-p
        (cdr subsequences)
        result))
    (equal subsequences nil)))

(defun verina-advanced-24-length-of-lis-postcond
    (nums result)
  (let* ((all-subsequences
          (verina-advanced-24-subsequences nums))
         (all-increasing
          (verina-advanced-24-filter-increasing
           all-subsequences)))
    (and
     (integerp result)
     (verina-advanced-24-some-length-equal-p
      all-increasing
      result)
     (verina-advanced-24-all-lengths-at-most-p
      all-increasing
      result))))

;; The source proof-valued precondition argument is erased from computation;
;; its predicate remains an explicit hypothesis of this correctness statement.

(defun
    verina-advanced-24-length-of-lis-spec-satisfied-statement
    (nums)
  (implies
   (and
    (verina-advanced-24-integer-listp nums)
    (verina-advanced-24-length-of-lis-precond nums))
   (verina-advanced-24-length-of-lis-postcond
    nums
    (verina-advanced-24-length-of-lis nums))))

(value-triple :itpeval-statement-checked)
:q
