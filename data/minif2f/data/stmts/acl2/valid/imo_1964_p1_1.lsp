;; Statement-only formalization of miniF2F corpus artifact imo_1964_p1_1:
;; for every natural number n, if 7 divides 2^n - 1, then 3 divides n.
;; This file contains no proof.

(in-package "ACL2")

(defun imo-1964-p1-1-statement (n)
  (implies
   (and (natp n)
        (equal (mod (- (expt 2 n) 1) 7) 0))
   (equal (mod n 3) 0)))

(value-triple :itpeval-statement-checked)
:q
