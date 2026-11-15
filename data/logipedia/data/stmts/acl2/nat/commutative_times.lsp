;; Statement-only formalization of Logipedia corpus artifact
;; nat.commutative_times, catalog title "nat.commutative_times":
;; commutativity of multiplication on the natural numbers. This file contains
;; no proof.

(in-package "ACL2")

(defun logipedia-nat-commutative-times-statement (x y)
  (implies
   (and (natp x)
        (natp y))
   (equal (* x y)
          (* y x))))

(value-triple :itpeval-statement-checked)
:q
