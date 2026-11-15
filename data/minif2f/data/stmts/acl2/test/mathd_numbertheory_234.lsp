;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_234: natural-number digits a and b satisfying the stated
;; bounds and (10*a + b)^3 = 912673 have a + b = 16. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-234-statement (a b)
  (implies
   (and (natp a)
        (natp b)
        (<= 1 a)
        (<= a 9)
        (<= b 9)
        (equal (expt (+ (* 10 a) b) 3)
               912673))
   (equal (+ a b) 16)))

(value-triple :itpeval-statement-checked)
:q
