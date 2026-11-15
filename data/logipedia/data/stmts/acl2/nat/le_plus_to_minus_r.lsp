;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_plus_to_minus_r, catalog title "nat.le_plus_to_minus_r": for
;; natural numbers, a + b <= c implies a <= c - b, where subtraction is
;; truncated at zero. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-le-plus-to-minus-r-statement ()
  (forall (a b c)
    (implies
     (and (natp a)
          (natp b)
          (natp c))
     (implies
      (<= (+ a b) c)
      (<= a (nfix (- c b)))))))

(value-triple :itpeval-statement-checked)
:q
