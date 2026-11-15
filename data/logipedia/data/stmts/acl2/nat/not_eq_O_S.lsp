;; Statement-only formalization of Logipedia corpus artifact nat.not_eq_O_S,
;; catalog title "nat.not_eq_O_S": zero is unequal to the successor of every
;; natural number. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-eq-o-s-statement ()
  (forall (n)
    (implies
     (natp n)
     (not (equal 0 (+ 1 n))))))

(value-triple :itpeval-statement-checked)
:q
