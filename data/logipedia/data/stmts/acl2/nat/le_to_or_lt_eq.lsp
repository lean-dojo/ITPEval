;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_to_or_lt_eq, catalog title "nat.le_to_or_lt_eq": for all natural
;; numbers n and m, n <= m implies that n < m or n = m. This file contains
;; no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-le-to-or-lt-eq-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (<= n m)
      (or (< n m)
          (equal n m))))))

(value-triple :itpeval-statement-checked)
:q
