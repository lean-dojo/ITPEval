;; Statement-only formalization of miniF2F corpus artifact aime_1983_p9:
;; for 0 < x < pi, the expression (9*x^2*sin(x)^2 + 4)/(x*sin(x))
;; is at least 12. This file contains no proof.
;;
;; Put y = x*sin(x), so the displayed expression is 9*y + 4/y. The source
;; interval makes y positive. Conversely, every real y in (0,1] equals
;; x*sin(x) for some x in (0,pi/2], by continuity and the endpoint values
;; 0 and pi/2. Thus the source statement implies the universal inequality
;; below on (0,1]. For the reverse direction, if a source value y exceeds 1,
;; set z = 4/(9*y). Then 0 < z < 1 and 9*z + 4/z = 9*y + 4/y, so the
;; restricted universal inequality gives the source conclusion as well.
;;
;; Finally, exact rationals are dense in (0,1], and 9*y + 4/y is continuous
;; there. A strict real counterexample would therefore yield a rational one,
;; while the real statement immediately specializes to rationals. Hence this
;; ACL2 predicate is bidirectionally equivalent to the source proposition.

(in-package "ACL2")

(defun aime-1983-p9-statement (y)
  (implies
   (and (rationalp y)
        (< 0 y)
        (<= y 1))
   (<= 12
       (/ (+ (* 9 (expt y 2))
             4)
          y))))

(value-triple :itpeval-statement-checked)
:q
