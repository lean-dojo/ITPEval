;; Statement-only formalization of miniF2F corpus artifact
;; induction_12dvd4expnp1p20: for every natural number n, 12 divides
;; 4^(n+1) + 20. This file contains no proof.

(in-package "ACL2")

(defun induction-12dvd4expnp1p20-statement (n)
  (implies (natp n)
           (equal (mod (+ (expt 4 (+ n 1))
                          20)
                       12)
                  0)))

(value-triple :itpeval-statement-checked)
:q
