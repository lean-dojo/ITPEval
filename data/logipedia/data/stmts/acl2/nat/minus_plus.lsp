;; Statement-only formalization of Logipedia corpus artifact nat.minus_plus,
;; catalog title "nat.minus_plus": for all natural numbers n, m, and p,
;; subtracting m and then p equals subtracting their sum, using truncated
;; natural subtraction. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-plus-statement ()
  (forall (n m p)
    (implies
     (and (natp n)
          (natp m)
          (natp p))
     (equal
      (nfix (- (nfix (- n m)) p))
      (nfix (- n (+ m p)))))))

(value-triple :itpeval-statement-checked)
:q
