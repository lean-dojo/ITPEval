;; Statement-only formalization of VERINA corpus artifact verina_advanced_2,
;; "LongestCommonSubsequence": a row-by-row dynamic program computes the
;; maximum length among the common subsequences of two integer arrays.
;; This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-2-integer-listp (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (verina-advanced-2-integer-listp (cdr xs)))
    (equal xs nil)))

;; The source precondition is True; the Array Int domains are explicit in the
;; final correctness statement.

(defun verina-advanced-2-longest-common-subsequence-precond (a b)
  (declare (ignore a b))
  t)

(defun verina-advanced-2-int-max (x y)
  (if (< x y) y x))

;; An Array is represented by its element list.  The zero row has one entry
;; for column zero and one for every element of b.

(defun verina-advanced-2-zero-row (b)
  (if (consp b)
      (cons 0 (verina-advanced-2-zero-row (cdr b)))
    (list 0)))

;; PREVIOUS-TAIL begins at the previous row's entry for the column immediately
;; left of the current cell.  Thus its first two entries are the diagonal and
;; upper neighbors, while LEFT is the already-updated current-row neighbor.
;; This is exactly the source's increasing-j inner loop.

(defun verina-advanced-2-build-row-aux
    (a-element remaining-b previous-tail left)
  (if (consp remaining-b)
      (let* ((diagonal (car previous-tail))
             (upper (car (cdr previous-tail)))
             (new-value
              (if (equal a-element (car remaining-b))
                  (+ diagonal 1)
                (verina-advanced-2-int-max upper left))))
        (cons
         new-value
         (verina-advanced-2-build-row-aux
          a-element
          (cdr remaining-b)
          (cdr previous-tail)
          new-value)))
    nil))

(defun verina-advanced-2-build-row
    (a-element b previous-row)
  (cons
   0
   (verina-advanced-2-build-row-aux
    a-element b previous-row 0)))

;; Folding over a in order reproduces the source's increasing-i outer loop.

(defun verina-advanced-2-fold-dp-rows
    (remaining-a b previous-row)
  (if (consp remaining-a)
      (verina-advanced-2-fold-dp-rows
       (cdr remaining-a)
       b
       (verina-advanced-2-build-row
        (car remaining-a) b previous-row))
    previous-row))

(defun verina-advanced-2-last-value (xs)
  (if (consp xs)
      (if (consp (cdr xs))
          (verina-advanced-2-last-value (cdr xs))
        (car xs))
    0))

(defun verina-advanced-2-longest-common-subsequence (a b)
  (verina-advanced-2-last-value
   (verina-advanced-2-fold-dp-rows
    a b (verina-advanced-2-zero-row b))))

;; The following definitions reproduce the postcondition's local allSubseq
;; function.  For each array element x, the fold appends to ACC a copy of ACC
;; with x prepended to every subsequence, then reverses every final subsequence.

(defun verina-advanced-2-prepend-to-each (x subsequences)
  (if (consp subsequences)
      (cons
       (cons x (car subsequences))
       (verina-advanced-2-prepend-to-each
        x (cdr subsequences)))
    nil))

(defun verina-advanced-2-all-subseq-fold
    (remaining-array accumulator)
  (if (consp remaining-array)
      (verina-advanced-2-all-subseq-fold
       (cdr remaining-array)
       (append
        accumulator
        (verina-advanced-2-prepend-to-each
         (car remaining-array) accumulator)))
    accumulator))

(defun verina-advanced-2-reverse-each (subsequences)
  (if (consp subsequences)
      (cons
       (reverse (car subsequences))
       (verina-advanced-2-reverse-each
        (cdr subsequences)))
    nil))

(defun verina-advanced-2-all-subseq (array)
  (verina-advanced-2-reverse-each
   (verina-advanced-2-all-subseq-fold
    array (list nil))))

(defun verina-advanced-2-common-subseq
    (subsequences-a subsequences-b)
  (if (consp subsequences-a)
      (if (member-equal (car subsequences-a) subsequences-b)
          (cons
           (car subsequences-a)
           (verina-advanced-2-common-subseq
            (cdr subsequences-a) subsequences-b))
        (verina-advanced-2-common-subseq
         (cdr subsequences-a) subsequences-b))
    nil))

(defun verina-advanced-2-subseq-lengths (subsequences)
  (if (consp subsequences)
      (cons
       (len (car subsequences))
       (verina-advanced-2-subseq-lengths
        (cdr subsequences)))
    nil))

(defun verina-advanced-2-all-lengths-at-most-p
    (lengths result)
  (if (consp lengths)
      (and
       (<= (car lengths) result)
       (verina-advanced-2-all-lengths-at-most-p
        (cdr lengths) result))
    (equal lengths nil)))

(defun verina-advanced-2-longest-common-subsequence-postcond
    (a b result)
  (let* ((subseq-a
          (verina-advanced-2-all-subseq a))
         (subseq-b
          (verina-advanced-2-all-subseq b))
         (common-subseq-lengths
          (verina-advanced-2-subseq-lengths
           (verina-advanced-2-common-subseq
            subseq-a subseq-b))))
    (and
     (integerp result)
     (if (member-equal result common-subseq-lengths)
         t
       nil)
     (verina-advanced-2-all-lengths-at-most-p
      common-subseq-lengths result))))

(defun
    verina-advanced-2-longest-common-subsequence-spec-satisfied-statement
    (a b)
  (implies
   (and
    (verina-advanced-2-integer-listp a)
    (verina-advanced-2-integer-listp b)
    (verina-advanced-2-longest-common-subsequence-precond
     a b))
   (verina-advanced-2-longest-common-subsequence-postcond
    a
    b
    (verina-advanced-2-longest-common-subsequence a b))))

(value-triple :itpeval-statement-checked)
:q
