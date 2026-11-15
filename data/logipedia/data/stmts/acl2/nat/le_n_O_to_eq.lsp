;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_n_O_to_eq, catalog title "nat.le_n_O_to_eq": every natural number
;; less than or equal to zero is equal to zero. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-n-o-to-eq-statement (n)
  (implies
   (and
    (natp n)
    (<= n 0))
   (equal 0 n)))

(value-triple :itpeval-statement-checked)
:q
