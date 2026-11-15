;; Statement-only formalization of Logipedia corpus artifact nat.minus_to_plus,
;; catalog title "nat.minus_to_plus": for all natural numbers n, m, and p, if
;; m is at most n and the truncated difference n - m equals p, then n equals
;; m + p. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-to-plus-statement ()
  (forall (n m p)
    (implies
     (and (natp n)
          (natp m)
          (natp p))
     (implies
      (<= m n)
      (implies
       (equal (nfix (- n m)) p)
       (equal n (+ m p)))))))

(value-triple :itpeval-statement-checked)
:q
