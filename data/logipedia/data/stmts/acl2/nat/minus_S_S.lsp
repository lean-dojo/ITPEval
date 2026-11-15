;; Statement-only formalization of Logipedia corpus artifact nat.minus_S_S,
;; catalog title "nat.minus_S_S": for all natural numbers n and m, truncated
;; natural subtraction of their successors equals n minus m. This file
;; contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-s-s-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (nfix (- (+ n 1) (+ m 1)))
      (nfix (- n m))))))

(value-triple :itpeval-statement-checked)
:q
