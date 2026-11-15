;; Statement-only formalization of miniF2F corpus artifact
;; induction_divisibility_3divnto3m2n: for every natural number n, 3
;; divides n cubed plus 2*n. This file contains no proof.

(in-package "ACL2")

(defun induction-divisibility-3divnto3m2n-statement (n)
  (implies
   (natp n)
   (equal (mod (+ (expt n 3) (* 2 n)) 3)
          0)))

(value-triple :itpeval-statement-checked)
:q
