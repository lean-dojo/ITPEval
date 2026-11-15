;; Statement-only formalization of Logipedia corpus artifact nat.minus_n_n,
;; catalog title "nat.minus_n_n": subtracting a natural number from itself
;; yields zero. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-minus (n m)
  (nfix (- n m)))

(defun logipedia-nat-minus-n-n-statement (n)
  (implies
   (natp n)
   (equal 0 (logipedia-nat-minus n n))))

(value-triple :itpeval-statement-checked)
:q
