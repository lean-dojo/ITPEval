;; Statement-only formalization of Logipedia corpus artifact
;; nat.lt_to_not_zero, catalog title "nat.lt_to_not_zero": for all natural
;; numbers n and m, n < m implies that m is nonzero. This file contains
;; no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-lt-to-not-zero-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (< n m)
      (not (equal m 0))))))

(value-triple :itpeval-statement-checked)
:q
