;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_xsqpysqintdenomeq: rational numbers x and y whose sum of
;; squares has denominator 1 have equal normalized denominators. This file
;; contains no proof.

(in-package "ACL2")

(defun numbertheory-xsqpysqintdenomeq-statement (x y)
  (implies
   (and (rationalp x)
        (rationalp y)
        (equal (denominator (+ (* x x) (* y y))) 1))
   (equal (denominator x)
          (denominator y))))

(value-triple :itpeval-statement-checked)
:q
