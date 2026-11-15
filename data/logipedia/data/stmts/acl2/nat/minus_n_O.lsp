;; Statement-only formalization of Logipedia corpus artifact nat.minus_n_O,
;; catalog title "nat.minus_n_O": for every natural number n, truncated
;; natural subtraction by zero leaves n unchanged. This file contains no
;; proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-n-o-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      n
      (nfix (- n 0))))))

(value-triple :itpeval-statement-checked)
:q
