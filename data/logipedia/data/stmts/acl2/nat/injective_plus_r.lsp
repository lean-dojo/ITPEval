;; Statement-only formalization of Logipedia corpus artifact
;; nat.injective_plus_r, catalog title "nat.injective_plus_r": for every
;; natural number n, addition of n on the left is injective on natural
;; numbers. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-injective-plus-r-statement (n x y)
  (implies
   (and (natp n)
        (natp x)
        (natp y)
        (equal (+ n x)
               (+ n y)))
   (equal x y)))

(value-triple :itpeval-statement-checked)
:q
