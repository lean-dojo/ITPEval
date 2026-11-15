;; Statement-only formalization of Logipedia corpus artifact nat.lt_to_le,
;; catalog title "nat.lt_to_le": for all natural numbers x and y, x < y
;; implies x <= y. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-lt-to-le-statement (x y)
  (implies
   (and (natp x)
        (natp y))
   (implies
    (< x y)
    (<= x y))))

(value-triple :itpeval-statement-checked)
:q
