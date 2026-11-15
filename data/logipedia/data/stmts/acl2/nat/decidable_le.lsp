;; Statement-only formalization of Logipedia corpus artifact nat.decidable_le,
;; catalog title "nat.decidable_le": the natural-number less-than-or-equal
;; relation is decidable for every pair of natural numbers. This file contains
;; no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-decidable-le-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (or (<= n m)
         (not (<= n m))))))

(value-triple :itpeval-statement-checked)
:q
