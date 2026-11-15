;; Statement-only formalization of miniF2F corpus artifact imo_1990_p3:
;; a natural number n at least 2 whose square divides 2^n + 1 must equal 3.
;; This file contains no proof.

(in-package "ACL2")

(defun imo-1990-p3-statement (n)
  (implies
   (and (natp n)
        (<= 2 n)
        (equal (mod (+ (expt 2 n) 1)
                    (expt n 2))
               0))
   (equal n 3)))

(value-triple :itpeval-statement-checked)
:q
