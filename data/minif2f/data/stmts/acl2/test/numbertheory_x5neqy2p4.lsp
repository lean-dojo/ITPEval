;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_x5neqy2p4: for all integers x and y, x^5 is not equal
;; to y^2 + 4. This file contains no proof.

(in-package "ACL2")

(defun numbertheory-x5neqy2p4-statement (x y)
  (implies
   (and (integerp x)
        (integerp y))
   (not
    (equal (expt x 5)
           (+ (expt y 2) 4)))))

(value-triple :itpeval-statement-checked)
:q
