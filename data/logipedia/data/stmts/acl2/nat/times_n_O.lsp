;; Statement-only formalization of Logipedia corpus artifact nat.times_n_O,
;; catalog title "nat.times_n_O": for every natural number n, multiplying n
;; by zero yields zero. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-times-n-o-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      0
      (* n 0)))))

(value-triple :itpeval-statement-checked)
:q
