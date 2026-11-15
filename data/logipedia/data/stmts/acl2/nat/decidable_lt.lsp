;; Statement-only formalization of Logipedia corpus artifact nat.decidable_lt,
;; catalog title "nat.decidable_lt": the strict order on natural numbers is
;; decidable for every pair of natural numbers. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-decidable-lt-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (or (< n m)
         (not (< n m))))))

(value-triple :itpeval-statement-checked)
:q
