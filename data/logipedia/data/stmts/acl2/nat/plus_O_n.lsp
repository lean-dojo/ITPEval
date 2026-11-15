;; Statement-only formalization of Logipedia corpus artifact nat.plus_O_n,
;; catalog title "nat.plus_O_n": for every natural number n, adding zero on
;; the left leaves n unchanged. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-plus-o-n-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      n
      (+ 0 n)))))

(value-triple :itpeval-statement-checked)
:q
