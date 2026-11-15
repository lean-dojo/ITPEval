;; Statement-only formalization of Logipedia corpus artifact
;; nat.distributive_times_minus, catalog title
;; "nat.distributive_times_minus": left multiplication on natural numbers
;; distributes over truncated subtraction. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-distributive-times-minus-statement ()
  (forall (a b c)
    (implies
     (and (natp a)
          (natp b)
          (natp c))
     (equal
      (* a (nfix (- b c)))
      (nfix (- (* a b) (* a c)))))))

(value-triple :itpeval-statement-checked)
:q
