;; Statement-only formalization of Logipedia corpus artifact nat.times_n_1,
;; catalog title "nat.times_n_1": for every natural number n, multiplying n
;; by one leaves n unchanged. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-times-n-1-statement (n)
  (implies
   (natp n)
   (equal n (* n 1))))

(value-triple :itpeval-statement-checked)
:q
