;; Statement-only formalization of Logipedia corpus artifact nat.lt_plus_Sn_r,
;; catalog title "nat.lt_plus_Sn_r": every natural number a is strictly less
;; than (a + x) + (n + 1) for natural numbers x and n. This file contains no
;; proof.

(in-package "ACL2")

(defun logipedia-nat-lt-plus-sn-r-statement (a x n)
  (implies
   (and (natp a)
        (natp x)
        (natp n))
   (< a (+ (+ a x) (1+ n)))))

(value-triple :itpeval-statement-checked)
:q
