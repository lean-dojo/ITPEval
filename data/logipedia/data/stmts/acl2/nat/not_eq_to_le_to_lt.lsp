;; Statement-only formalization of Logipedia corpus artifact
;; nat.not_eq_to_le_to_lt, catalog title "nat.not_eq_to_le_to_lt": for all
;; natural numbers n and m, if n is not equal to m and n <= m, then n < m.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-eq-to-le-to-lt-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (not (equal n m))
      (implies
       (<= n m)
       (< n m))))))

(value-triple :itpeval-statement-checked)
:q
