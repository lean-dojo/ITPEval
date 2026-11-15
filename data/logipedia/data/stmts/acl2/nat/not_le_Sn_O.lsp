;; Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_O,
;; catalog title "nat.not_le_Sn_O": no successor of a natural number is less
;; than or equal to zero. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-le-sn-o-statement ()
  (forall (n)
    (implies
     (natp n)
     (not (<= (1+ n) 0)))))

(value-triple :itpeval-statement-checked)
:q
