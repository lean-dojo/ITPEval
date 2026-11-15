;; Statement-only formalization of Logipedia corpus artifact
;; nat.minus_plus_m_m, catalog title "nat.minus_plus_m_m": for all natural
;; numbers n and m, subtracting m from n plus m yields n, using truncated
;; natural subtraction. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-plus-m-m-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (equal n
            (nfix (- (+ n m) m))))))

(value-triple :itpeval-statement-checked)
:q
