;; Statement-only formalization of Logipedia corpus artifact nat.le_S,
;; catalog title "nat.le_S": natural-number order is preserved when the upper
;; bound is replaced by its successor. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-s-statement (n m)
  (implies
   (and (natp n)
        (natp m)
        (<= n m))
   (<= n (+ 1 m))))

(value-triple :itpeval-statement-checked)
:q
