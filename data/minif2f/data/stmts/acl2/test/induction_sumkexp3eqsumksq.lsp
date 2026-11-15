;; Statement-only formalization of miniF2F corpus artifact
;; induction_sumkexp3eqsumksq: for every natural number n, the sum of k^3
;; over 0 <= k < n equals the square of the sum of k over the same range.
;; This file contains no proof.

(in-package "ACL2")

(defun induction-sumkexp3eqsumksq-sum-powers (n power)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (induction-sumkexp3eqsumksq-sum-powers (- n 1) power)
       (expt (- n 1) power))))

(defun induction-sumkexp3eqsumksq-statement (n)
  (implies
   (natp n)
   (equal
    (induction-sumkexp3eqsumksq-sum-powers n 3)
    (expt (induction-sumkexp3eqsumksq-sum-powers n 1) 2))))

(value-triple :itpeval-statement-checked)
:q
