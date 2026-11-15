;; Statement-only formalization of miniF2F corpus artifact
;; algebra_amgm_prod1toneq1_sum1tongeqn: every finite sequence of
;; nonnegative real numbers with product one has sum at least its length.
;; This file contains no proof.
;;
;; A length-n list is equivalent to the restriction of the source function
;; to indices below n; conversely, extending the list by zeros gives a
;; globally nonnegative function on the naturals. The real statement implies
;; the rational instance below. For the converse, a real counterexample must
;; have n positive and every entry positive. For n at least two, approximate
;; its first n-1 entries by positive rationals and set the last entry to the
;; reciprocal of their product. This preserves product one exactly, and
;; continuity preserves the strict counterexample sum < n. The cases n = 0
;; and n = 1 are immediate. Thus this exact-rational encoding is
;; bidirectionally equivalent to the real theorem.

(in-package "ACL2")

(defun algebra-amgm-nonnegative-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (<= 0 (car values))
           (algebra-amgm-nonnegative-rational-list-p (cdr values)))
    (equal values nil)))

(defun algebra-amgm-sum (values)
  (if (consp values)
      (+ (car values)
         (algebra-amgm-sum (cdr values)))
    0))

(defun algebra-amgm-product (values)
  (if (consp values)
      (* (car values)
         (algebra-amgm-product (cdr values)))
    1))

(defun algebra-amgm-prod1toneq1-sum1tongeqn-statement (values n)
  (implies
   (and (natp n)
        (algebra-amgm-nonnegative-rational-list-p values)
        (equal (len values) n)
        (equal (algebra-amgm-product values) 1))
   (<= n (algebra-amgm-sum values))))

(value-triple :itpeval-statement-checked)
:q
