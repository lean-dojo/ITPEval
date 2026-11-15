;; Statement-only formalization of miniF2F corpus artifact
;; induction_divisibility_3div2tooddnp1: for every natural number n, 3
;; divides 2 raised to the odd exponent 2*n + 1, plus 1. This file contains
;; no proof.

(in-package "ACL2")

(defun induction-divisibility-3div2tooddnp1-statement (n)
  (implies
   (natp n)
   (equal (mod (+ (expt 2 (+ (* 2 n) 1)) 1) 3)
          0)))

(value-triple :itpeval-statement-checked)
:q
