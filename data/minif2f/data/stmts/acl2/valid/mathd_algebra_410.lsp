;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_410:
;; for real numbers x and y, if y = x^2 - 6*x + 13, then y is at least 4.
;; This file contains no proof.
;;
;; The exact-rational statement below is bidirectionally equivalent to the
;; real statement. The real theorem immediately restricts to rational x and
;; y. Conversely, a real counterexample would make the continuous polynomial
;; x^2 - 6*x + 9 negative at some real x and hence throughout a neighborhood
;; containing a rational x; the defining polynomial then gives a rational y
;; and thus a rational counterexample.

(in-package "ACL2")

(defun mathd-algebra-410-statement (x y)
  (implies
   (and (rationalp x)
        (rationalp y)
        (equal y
               (+ (- (expt x 2)
                     (* 6 x))
                  13)))
   (<= 4 y)))

(value-triple :itpeval-statement-checked)
:q
