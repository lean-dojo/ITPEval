;; Statement-only formalization of Logipedia corpus artifact nat.le_n,
;; catalog title "nat.le_n": every natural number is less than or equal to
;; itself. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-n-statement (n)
  (implies
   (natp n)
   (<= n n)))

(value-triple :itpeval-statement-checked)
:q
