;; Statement-only formalization of Logipedia corpus artifact
;; nat.lt_to_le_to_lt_times, catalog title "nat.lt_to_le_to_lt_times":
;; for natural numbers n, m, p, and q, n < m, p <= q, and 0 < q imply
;; n*p < m*q. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-lt-to-le-to-lt-times-statement (n m p q)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (natp q))
   (implies
    (< n m)
    (implies
     (<= p q)
     (implies
      (< 0 q)
      (< (* n p)
         (* m q)))))))

(value-triple :itpeval-statement-checked)
:q
