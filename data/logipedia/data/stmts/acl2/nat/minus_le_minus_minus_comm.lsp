;; Statement-only formalization of Logipedia corpus artifact
;; nat.minus_le_minus_minus_comm, catalog title
;; "nat.minus_le_minus_minus_comm": for natural numbers a, b, and c with
;; c at most b, subtracting b - c from a equals subtracting b from a + c.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-le-minus-minus-comm-statement ()
  (forall (b c a)
    (implies
     (and
      (natp b)
      (natp c)
      (natp a))
     (implies
      (<= c b)
      (equal
       (nfix (- a (nfix (- b c))))
       (nfix (- (+ a c) b)))))))

(value-triple :itpeval-statement-checked)
:q
