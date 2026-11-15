;; Statement-only formalization of Logipedia corpus artifact nat.injective_S,
;; catalog title "nat.injective_S": the successor function on natural numbers
;; is injective. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-injective-s-statement (x y)
  (implies
   (and (natp x)
        (natp y)
        (equal (+ 1 x)
               (+ 1 y)))
   (equal x y)))

(value-triple :itpeval-statement-checked)
:q
