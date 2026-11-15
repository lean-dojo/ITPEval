;; Statement-only formalization of Logipedia corpus artifact nat.not_eq_S,
;; catalog title "nat.not_eq_S": unequal natural numbers have unequal
;; successors. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-eq-s-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (not (equal n m))
      (not (equal (+ 1 n)
                  (+ 1 m)))))))

(value-triple :itpeval-statement-checked)
:q
