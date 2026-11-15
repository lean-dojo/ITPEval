;; Statement-only formalization of miniF2F corpus artifact
;; algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3: for integers x, y,
;; and z satisfying the stated sum-of-squared-differences identity,
;; x + y + z + 6 divides the sum of their cubes. This file contains no proof.

(in-package "ACL2")

(defun algebra-xmysqpymzsqpzmxsqeqxyz-xpypzp6dvdx3y3z3-statement (x y z)
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp z)
    (equal
     (+ (+ (expt (- x y) 2)
           (expt (- y z) 2))
        (expt (- z x) 2))
     (* (* x y) z)))
   (let
       ((divisor (+ (+ (+ x y) z) 6))
        (dividend
         (+ (+ (expt x 3)
               (expt y 3))
            (expt z 3))))
     (if (equal divisor 0)
         (equal dividend 0)
       (equal (mod dividend divisor) 0)))))

(value-triple :itpeval-statement-checked)
:q
