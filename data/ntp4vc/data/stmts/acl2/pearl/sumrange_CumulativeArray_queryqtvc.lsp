;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sumrange_CumulativeArray_queryqtvc: the cumulative-array range-query
;; verification condition, relating prefix-sum differences to the half-open
;; integer-array sum. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper finite integer lists represent Why3 arrays of mathematical integers.

(defun sumrange-query-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (sumrange-query-integer-list-p (cdr xs)))))

;; Int.toNat sends negative indices to zero, and the exported total list lookup
;; returns the integer default zero outside the list.

(defun sumrange-query-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun sumrange-query-nth-int (index xs)
  (let ((value
         (nth
          (sumrange-query-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; On every source-valid interval this recursion is definitionally equivalent
;; to ArraySum.sum, summing exactly the entries with LOWER <= index < UPPER.

(defun sumrange-query-range-sum (xs lower upper)
  (declare
   (xargs :measure
          (nfix (- upper lower))))
  (if (or
       (not (integerp lower))
       (not (integerp upper))
       (<= upper lower))
      0
    (+
     (sumrange-query-nth-int (- upper 1) xs)
     (sumrange-query-range-sum
      xs lower (- upper 1)))))

;; The source cumulative-array invariant, retaining its universal quantifier
;; over every mathematical integer index.

(defun-sk sumrange-query-cumulative-entries-p (c a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len c)))
      (equal
       (sumrange-query-nth-int index c)
       (sumrange-query-range-sum a 0 index))))))

(defun sumrange-query-is-cumulative-array-for-p (c a)
  (and
   (sumrange-query-integer-list-p c)
   (sumrange-query-integer-list-p a)
   (equal (len c) (+ (len a) 1))
   (sumrange-query-cumulative-entries-p c a)))

;; The arguments encode the source theorem's universally quantified typed
;; parameters. The antecedent is exactly its four named assumptions, and the
;; conclusion retains all four bounds and the range-sum equality.

(defun
  ntp4vc-pearl-sumrange-cumulativearray-queryqtvc-statement
  (c a i j)
  (implies
   (and
    (integerp i)
    (integerp j)
    (sumrange-query-is-cumulative-array-for-p c a)
    (<= 0 i)
    (<= i j)
    (< j (len c)))
   (and
    (<= 0 i)
    (< i (len c))
    (<= 0 j)
    (< j (len c))
    (equal
     (-
      (sumrange-query-nth-int j c)
      (sumrange-query-nth-int i c))
     (sumrange-query-range-sum a i j)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
