;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_284:
;; natural numbers a and b satisfying the given digit bounds and equation have
;; 10*a + b equal to 18. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-284-statement (a b)
  (implies
   (and (natp a)
        (natp b)
        (<= 1 a)
        (<= a 9)
        (<= b 9)
        (equal (+ (* 10 a) b)
               (* 2 (+ a b))))
   (equal (+ (* 10 a) b) 18)))

(value-triple :itpeval-statement-checked)
:q
