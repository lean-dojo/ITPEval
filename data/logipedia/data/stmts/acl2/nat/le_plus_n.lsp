;; Statement-only formalization of Logipedia corpus artifact nat.le_plus_n,
;; catalog title "nat.le_plus_n": for all natural numbers n and m, m is at
;; most n + m. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-plus-n-statement (n m)
  (implies
   (and (natp n)
        (natp m))
   (<= m (+ n m))))

(value-triple :itpeval-statement-checked)
:q
