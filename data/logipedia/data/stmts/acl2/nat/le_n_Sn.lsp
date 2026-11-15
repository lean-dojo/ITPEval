;; Statement-only formalization of Logipedia corpus artifact nat.le_n_Sn,
;; catalog title "nat.le_n_Sn": every natural number is less than or equal
;; to its successor. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-n-sn-statement (n)
  (implies
   (natp n)
   (<= n (+ 1 n))))

(value-triple :itpeval-statement-checked)
:q
