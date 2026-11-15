;; Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_n,
;; catalog title "nat.not_le_Sn_n": no successor of a natural number is less
;; than or equal to that natural number. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-le-sn-n-statement ()
  (forall (n)
    (implies
     (natp n)
     (not (<= (1+ n) n)))))

(value-triple :itpeval-statement-checked)
:q
