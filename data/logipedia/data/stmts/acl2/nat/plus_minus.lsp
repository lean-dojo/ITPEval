;; Statement-only formalization of Logipedia corpus artifact nat.plus_minus,
;; catalog title "nat.plus_minus": for all natural numbers m, n, and p, if
;; m <= n then (n - m) + p = (n + p) - m, with subtraction truncated at zero.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-plus-minus-statement ()
  (forall (m n p)
    (implies
     (and (natp m)
          (natp n)
          (natp p))
     (implies
      (<= m n)
      (equal (+ (nfix (- n m)) p)
             (nfix (- (+ n p) m)))))))

(value-triple :itpeval-statement-checked)
:q
