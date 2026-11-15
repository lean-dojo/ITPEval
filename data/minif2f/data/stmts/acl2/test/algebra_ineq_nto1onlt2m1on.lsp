;; Statement-only formalization of miniF2F artifact
;; algebra_ineq_nto1onlt2m1on: for each positive natural number n, the real
;; n-th root n^(1/n) is at most 2 - 1/n. ACL2 encodes this by the equivalent
;; exact rational inequality n <= (2 - 1/n)^n. This file contains no proof.

(in-package "ACL2")

(defun algebra-ineq-nto1onlt2m1on-statement (n)
  (implies (and (natp n)
                (< 0 n))
           (<= n
               (expt (- 2 (/ 1 n)) n))))

(value-triple :itpeval-statement-checked)
:q
