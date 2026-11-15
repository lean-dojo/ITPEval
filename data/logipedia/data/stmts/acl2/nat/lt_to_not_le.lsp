;; Statement-only formalization of Logipedia corpus artifact
;; nat.lt_to_not_le, catalog title "nat.lt_to_not_le": for all natural
;; numbers n and m, n < m implies that m is not less than or equal to n.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-lt-to-not-le-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (< n m)
      (not (<= m n))))))

(value-triple :itpeval-statement-checked)
:q
