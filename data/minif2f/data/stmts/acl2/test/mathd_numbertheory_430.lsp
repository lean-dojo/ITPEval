;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_430: natural numbers a, b, and c from 1 through 9,
;; pairwise distinct and satisfying the stated addition, natural-subtraction,
;; and multiplication equations, have a + b + c = 8. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-430-statement (a b c)
  (implies
   (and (natp a)
        (natp b)
        (natp c)
        (<= 1 a)
        (<= a 9)
        (<= 1 b)
        (<= b 9)
        (<= 1 c)
        (<= c 9)
        (not (equal a b))
        (not (equal a c))
        (not (equal b c))
        (equal (+ a b) c)
        (equal (nfix (- (+ (* 10 a) a) b))
               (* 2 c))
        (equal (* c b)
               (+ (* 10 a) a a)))
   (equal (+ a b c) 8)))

(value-triple :itpeval-statement-checked)
:q
