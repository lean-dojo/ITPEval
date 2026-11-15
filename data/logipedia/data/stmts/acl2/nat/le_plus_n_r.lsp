;; Statement-only formalization of Logipedia corpus artifact nat.le_plus_n_r,
;; catalog title "nat.le_plus_n_r": for all natural numbers n and m, m is
;; less than or equal to m + n. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-plus-n-r-statement (n m)
  (implies
   (and (natp n)
        (natp m))
   (<= m (+ m n))))

(value-triple :itpeval-statement-checked)
:q
