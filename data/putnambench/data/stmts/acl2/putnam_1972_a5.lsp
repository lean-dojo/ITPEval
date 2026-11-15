;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_a5:
;; every natural number n greater than 1 fails to divide the integer 2^n - 1.
;; This file contains no proof.

(in-package "ACL2")

(defun putnambench-putnam-1972-a5-statement (n)
  (implies
   (and (natp n)
        (< 1 n))
   (not (equal (mod (- (expt 2 n) 1) n) 0))))

(value-triple :itpeval-statement-checked)
:q
