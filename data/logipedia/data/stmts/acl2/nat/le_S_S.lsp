;; Statement-only formalization of Logipedia corpus artifact nat.le_S_S,
;; catalog title "nat.le_S_S": successor preserves the less-than-or-equal
;; relation on natural numbers. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-s-s-statement (n m)
  (implies
   (and (natp n)
        (natp m)
        (<= n m))
   (<= (1+ n)
       (1+ m))))

(value-triple :itpeval-statement-checked)
:q
