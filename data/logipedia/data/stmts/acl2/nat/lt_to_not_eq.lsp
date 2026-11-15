;; Statement-only formalization of Logipedia corpus artifact
;; nat.lt_to_not_eq, catalog title "nat.lt_to_not_eq": for all natural
;; numbers n and m, n < m implies n is not equal to m. This file contains
;; no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-lt-to-not-eq-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (< n m)
      (not (equal n m))))))

(value-triple :itpeval-statement-checked)
:q
