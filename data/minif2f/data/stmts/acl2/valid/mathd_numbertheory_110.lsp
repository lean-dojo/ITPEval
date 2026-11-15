;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_110:
;; positive natural numbers a and b with b no greater than a and the specified
;; remainders modulo 10 have natural difference congruent to 6 modulo 10.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-110-statement (a b)
  (implies
   (and (natp a)
        (natp b)
        (< 0 a)
        (< 0 b)
        (<= b a)
        (equal (mod (+ a b) 10) 2)
        (equal (mod (+ (* 2 a) b) 10) 1))
   (equal (mod (nfix (- a b)) 10) 6)))

(value-triple :itpeval-statement-checked)
:q
