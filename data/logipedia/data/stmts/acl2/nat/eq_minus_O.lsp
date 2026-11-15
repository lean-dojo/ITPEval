;; Statement-only formalization of Logipedia corpus artifact nat.eq_minus_O,
;; catalog title "nat.eq_minus_O": for all natural numbers n and m, if n is
;; at most m, then their truncated natural difference n - m is zero.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-eq-minus-o-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (implies
      (<= n m)
      (equal (nfix (- n m)) 0)))))

(value-triple :itpeval-statement-checked)
:q
