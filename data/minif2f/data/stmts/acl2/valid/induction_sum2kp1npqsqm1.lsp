;; Statement-only formalization of miniF2F corpus artifact
;; induction_sum2kp1npqsqm1: for every natural number n, the sum of
;; 2*k + 3 over k = 0,...,n-1 equals (n + 1)^2 - 1. This file contains no
;; proof.

(in-package "ACL2")

(defun induction-sum2kp1npqsqm1-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (* 2 (- n 1))
       3
       (induction-sum2kp1npqsqm1-sum (- n 1)))))

(defun induction-sum2kp1npqsqm1-statement (n)
  (implies
   (natp n)
   (equal
    (induction-sum2kp1npqsqm1-sum n)
    (- (expt (+ n 1) 2) 1))))

(value-triple :itpeval-statement-checked)
:q
