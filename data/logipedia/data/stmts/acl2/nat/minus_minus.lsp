;; Statement-only formalization of Logipedia corpus artifact nat.minus_minus,
;; catalog title "nat.minus_minus": for natural numbers n, m, and p with
;; p <= m <= n, the natural-subtraction identity
;; p + (n - m) = n - (m - p) holds. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-minus-statement ()
  (forall (n m p)
    (implies
     (and (natp n)
          (natp m)
          (natp p))
     (implies
      (<= p m)
      (implies
       (<= m n)
       (equal
        (+ p (nfix (- n m)))
        (nfix (- n (nfix (- m p))))))))))

(value-triple :itpeval-statement-checked)
:q
