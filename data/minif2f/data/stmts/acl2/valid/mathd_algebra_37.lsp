;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_37:
;; for real x and y, if x + y = 7 and 3*x + y = 45, then
;; x^2 - y^2 = 217. This file contains no proof.

(in-package "ACL2")

;; The two source equations uniquely force x = 19 and y = -12. Thus every
;; satisfying real assignment lies in the exact rational subfield represented
;; by ACL2, while every encoded rational assignment embeds unchanged into the
;; reals. The rational guards therefore preserve the source implication in
;; both directions.
(defun mathd-algebra-37-statement (x y)
  (implies
   (and (rationalp x)
        (rationalp y)
        (equal (+ x y) 7)
        (equal (+ (* 3 x) y) 45))
   (equal (- (expt x 2)
             (expt y 2))
          217)))

(value-triple :itpeval-statement-checked)
:q
