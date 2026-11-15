;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_to_le_to_eq, catalog title "nat.le_to_le_to_eq": two natural
;; numbers that are each less than or equal to the other are equal. This file
;; contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-to-le-to-eq-statement (n m)
  (implies
   (and (natp n)
        (natp m))
   (implies
    (<= n m)
    (implies
     (<= m n)
     (equal n m)))))

(value-triple :itpeval-statement-checked)
:q
