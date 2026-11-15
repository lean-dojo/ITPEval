;; Statement-only formalization of miniF2F corpus artifact
;; algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4: complex numbers x and e
;; satisfying x + e = 7 and 2*x + e = 3 satisfy e = 11 and x = -4.
;; ACL2-NUMBERP is equivalent for this implication: subtracting the equations
;; forces x = -4 and then e = 11, so every satisfying source-complex tuple is
;; represented by ACL2's exact number domain, whose values embed in the
;; complex numbers. This file contains no proof.

(in-package "ACL2")

(defun algebra-2varlineareq-xpeeq7-2xpeeq3-eeq11-xeqn4-statement (x e)
  (implies
   (and (acl2-numberp x)
        (acl2-numberp e)
        (equal (+ x e) 7)
        (equal (+ (* 2 x) e) 3))
   (and (equal e 11)
        (equal x -4))))

(value-triple :itpeval-statement-checked)
:q
