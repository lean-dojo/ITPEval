;; Statement-only formalization of Logipedia corpus artifact nat.minus_le,
;; catalog title "nat.minus_le": for all natural numbers x and y, the
;; truncated natural difference x - y is at most x. This file contains no
;; proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-le-statement ()
  (forall (x y)
    (implies
     (and
      (natp x)
      (natp y))
     (<= (nfix (- x y)) x))))

(value-triple :itpeval-statement-checked)
:q
