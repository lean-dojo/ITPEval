;; Statement-only formalization of Logipedia corpus artifact nat.le_O_n,
;; catalog title "nat.le_O_n": zero is less than or equal to every natural
;; number. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-o-n-statement (n)
  (implies
   (natp n)
   (<= 0 n)))

(value-triple :itpeval-statement-checked)
:q
