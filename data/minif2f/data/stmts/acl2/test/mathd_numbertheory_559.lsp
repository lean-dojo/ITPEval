;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_559: natural numbers x and y with residues 2 modulo 3
;; and 4 modulo 5, and equal residues modulo 10, satisfy 14 <= x.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-559-statement (x y)
  (implies
   (and (natp x)
        (natp y)
        (equal (mod x 3) 2)
        (equal (mod y 5) 4)
        (equal (mod x 10) (mod y 10)))
   (<= 14 x)))

(value-triple :itpeval-statement-checked)
:q
