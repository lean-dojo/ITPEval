;; Statement-only formalization of Logipedia corpus artifact nat.plus_to_minus,
;; catalog title "nat.plus_to_minus": for all natural numbers n, m, and p,
;; n = m + p implies that truncated natural subtraction n - m equals p.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-plus-to-minus-statement ()
  (forall (n m p)
    (implies
     (and (natp n)
          (natp m)
          (natp p))
     (implies
      (equal n (+ m p))
      (equal (nfix (- n m))
             p)))))

(value-triple :itpeval-statement-checked)
:q
