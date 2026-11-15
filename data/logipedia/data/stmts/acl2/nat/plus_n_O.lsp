;; Statement-only formalization of Logipedia corpus artifact nat.plus_n_O,
;; catalog title "nat.plus_n_O": for every natural number n, adding zero on
;; the right leaves n unchanged. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-plus-n-o-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      n
      (+ n 0)))))

(value-triple :itpeval-statement-checked)
:q
