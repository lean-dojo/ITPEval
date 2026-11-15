;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_plus_minus_m_m, catalog title "nat.le_plus_minus_m_m": every
;; natural number n is at most its truncated difference n - m plus m.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-le-plus-minus-m-m-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (<= n
         (+ (nfix (- n m)) m)))))

(value-triple :itpeval-statement-checked)
:q
