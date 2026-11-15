;; Statement-only formalization of Logipedia corpus artifact nat.lt_O_S,
;; catalog title "nat.lt_O_S": zero is strictly less than the successor of
;; every natural number. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-lt-o-s-statement (n)
  (implies
   (natp n)
   (< 0 (+ 1 n))))

(value-triple :itpeval-statement-checked)
:q
