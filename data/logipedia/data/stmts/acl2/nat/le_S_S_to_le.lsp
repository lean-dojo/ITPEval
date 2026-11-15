;; Statement-only formalization of Logipedia corpus artifact nat.le_S_S_to_le,
;; catalog title "nat.le_S_S_to_le": successor order on natural numbers
;; implies the corresponding order of their predecessors. This file contains
;; no proof.

(in-package "ACL2")

(defun logipedia-nat-le-s-s-to-le-statement (n m)
  (implies
   (and (natp n)
        (natp m)
        (<= (1+ n)
            (1+ m)))
   (<= n m)))

(value-triple :itpeval-statement-checked)
:q
