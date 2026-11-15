;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_4x3m7y3neq2003: for all integers x and y,
;; 4*x^3 - 7*y^3 is not equal to 2003. This file contains no proof.

(in-package "ACL2")

(defun numbertheory-4x3m7y3neq2003-statement (x y)
  (implies
   (and (integerp x)
        (integerp y))
   (not
    (equal (- (* 4 (expt x 3))
              (* 7 (expt y 3)))
           2003))))

(value-triple :itpeval-statement-checked)
:q
