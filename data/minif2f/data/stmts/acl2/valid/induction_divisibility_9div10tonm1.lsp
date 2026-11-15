;; Statement-only formalization of miniF2F corpus artifact
;; induction_divisibility_9div10tonm1: for every positive natural number n,
;; 9 divides 10^n - 1. This file contains no proof.

(in-package "ACL2")

(defun induction-divisibility-9div10tonm1-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal (mod (- (expt 10 n) 1) 9)
          0)))

(value-triple :itpeval-statement-checked)
:q
