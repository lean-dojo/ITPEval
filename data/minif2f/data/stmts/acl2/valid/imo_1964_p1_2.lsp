;; Statement-only formalization of miniF2F corpus artifact imo_1964_p1_2:
;; for every natural number n, 7 does not divide 2^n + 1. This file contains
;; no proof.

(in-package "ACL2")

(defun imo-1964-p1-2-statement (n)
  (implies
   (natp n)
   (not (equal (mod (+ (expt 2 n) 1) 7)
               0))))

(value-triple :itpeval-statement-checked)
:q
