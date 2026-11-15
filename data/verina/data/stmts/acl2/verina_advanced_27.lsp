;; Statement-only formalization of VERINA corpus artifact verina_advanced_27,
;; "longestCommonSubsequence": a deterministic recursive computation returns
;; a Unicode string that satisfies the exhaustive longest-common-subsequence
;; contract. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-advanced-27-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-27-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-27-unicode-scalar-p (car s))
       (verina-advanced-27-string-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The two String binder domains are made
;; explicit in the final correctness statement.

(defun verina-advanced-27-longest-common-subsequence-precond
    (s1 s2)
  (declare (ignore s1 s2))
  t)

;; Under the canonical representation, String.data is the represented list.

(defun verina-advanced-27-to-char-list (s)
  s)

;; These two definitions reproduce foldl String.push "" exactly: one scalar
;; value is appended at each step, so the resulting string has precisely the
;; same character sequence as the input list.

(defun verina-advanced-27-string-push (acc c)
  (append acc (list c)))

(defun verina-advanced-27-from-char-list-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-27-from-char-list-fold
       (cdr remaining)
       (verina-advanced-27-string-push
        accumulator
        (car remaining)))
    accumulator))

(defun verina-advanced-27-from-char-list (characters)
  (verina-advanced-27-from-char-list-fold characters nil))

;; This is the source lcsAux recursion. In a mismatch, LEFT drops the first
;; character of xs and RIGHT drops the first character of ys. The >= test
;; preserves the source's deterministic choice of LEFT on equal lengths.

(defun verina-advanced-27-lcs-aux (xs ys)
  (declare
   (xargs
    :measure
    (+ (acl2-count xs) (acl2-count ys))))
  (if (endp xs)
      nil
    (if (endp ys)
        nil
      (if (equal (car xs) (car ys))
          (cons
           (car xs)
           (verina-advanced-27-lcs-aux
            (cdr xs)
            (cdr ys)))
        (let* ((left
                (verina-advanced-27-lcs-aux
                 (cdr xs)
                 ys))
               (right
                (verina-advanced-27-lcs-aux
                 xs
                 (cdr ys))))
          (if (>= (len left) (len right))
              left
            right))))))

;; The proof-valued True precondition argument is computationally irrelevant.
;; The remaining calls preserve the source let-bindings and helper connection.

(defun verina-advanced-27-longest-common-subsequence (s1 s2)
  (let* ((xs
          (verina-advanced-27-to-char-list s1))
         (ys
          (verina-advanced-27-to-char-list s2))
         (result-list
          (verina-advanced-27-lcs-aux xs ys)))
    (verina-advanced-27-from-char-list result-list)))

;; The following definitions reproduce the postcondition's local allSubseq.
;; Starting from [[]], each fold step appends a copy of the accumulator with
;; the current character prepended, and every resulting list is then reversed.

(defun verina-advanced-27-prepend-to-each
    (char-code subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (cons char-code (car subsequences))
       (verina-advanced-27-prepend-to-each
        char-code
        (cdr subsequences)))
    nil))

(defun verina-advanced-27-all-subseq-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-27-all-subseq-fold
       (cdr remaining)
       (append
        accumulator
        (verina-advanced-27-prepend-to-each
         (car remaining)
         accumulator)))
    accumulator))

(defun verina-advanced-27-reverse-each
    (subsequences)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-27-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-27-all-subseq (characters)
  (verina-advanced-27-reverse-each
   (verina-advanced-27-all-subseq-fold
    characters
    (list nil))))

;; List.filter with membership in subseq-b, preserving order and duplicates.

(defun verina-advanced-27-common-subseq
    (subseq-a subseq-b)
  (declare (xargs :measure (acl2-count subseq-a)))
  (if (consp subseq-a)
      (if (member-equal (car subseq-a) subseq-b)
          (cons
           (car subseq-a)
           (verina-advanced-27-common-subseq
            (cdr subseq-a)
            subseq-b))
        (verina-advanced-27-common-subseq
         (cdr subseq-a)
         subseq-b))
    nil))

(defun verina-advanced-27-contains-subseq-p
    (subsequences result)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (or
       (equal (car subsequences) result)
       (verina-advanced-27-contains-subseq-p
        (cdr subsequences)
        result))
    nil))

(defun verina-advanced-27-all-lengths-at-most-result-p
    (subsequences result)
  (declare (xargs :measure (acl2-count subsequences)))
  (if (consp subsequences)
      (and
       (<= (len (car subsequences)) (len result))
       (verina-advanced-27-all-lengths-at-most-result-p
        (cdr subsequences)
        result))
    t))

(defun verina-advanced-27-longest-common-subsequence-postcond
    (s1 s2 result)
  (let* ((subseq-a
          (verina-advanced-27-all-subseq
           (verina-advanced-27-to-char-list s1)))
         (subseq-b
          (verina-advanced-27-all-subseq
           (verina-advanced-27-to-char-list s2)))
         (common-subseq
          (verina-advanced-27-common-subseq
           subseq-a
           subseq-b)))
    (and
     (verina-advanced-27-string-p s1)
     (verina-advanced-27-string-p s2)
     (verina-advanced-27-string-p result)
     (verina-advanced-27-contains-subseq-p
      common-subseq
      (verina-advanced-27-to-char-list result))
     (verina-advanced-27-all-lengths-at-most-result-p
      common-subseq
      (verina-advanced-27-to-char-list result)))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves both Lean String binders and the source precondition,
;; while its conclusion applies the postcondition to the executable result.

(defun
    verina-advanced-27-longest-common-subsequence-spec-satisfied-statement
    (s1 s2)
  (implies
   (and
    (verina-advanced-27-string-p s1)
    (verina-advanced-27-string-p s2)
    (verina-advanced-27-longest-common-subsequence-precond
     s1
     s2))
   (verina-advanced-27-longest-common-subsequence-postcond
    s1
    s2
    (verina-advanced-27-longest-common-subsequence s1 s2))))

(value-triple :itpeval-statement-checked)
:q
