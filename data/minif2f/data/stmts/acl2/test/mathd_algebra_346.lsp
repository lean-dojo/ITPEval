;; Statement-only formalization of miniF2F artifact mathd_algebra_346:
;; the affine real functions f(x) = 2*x - 3 and g(x) = x + 1 satisfy
;; g(f(5) - 1) = 7. This file contains no proof.
;;
;; ACL2 is first-order, so the functions are represented by the observations
;; f(5) and g(f(5) - 1), the only function values used in the conclusion.
;; The antecedent is exactly the two source hypotheses instantiated at 5 and
;; f(5) - 1. Every source pair supplies these observations. Conversely, the
;; antecedent forces them to be 7 and 7, and they are realized by the source
;; functions f(x) = 2*x - 3 and g(x) = x + 1. Thus this observation
;; implication is bidirectionally equivalent to the source statement. The
;; equalities force exact integer values, so unrestricted ACL2 parameters do
;; not narrow the source real domain.

(in-package "ACL2")

(defun mathd-algebra-346-statement
    (f-at-5 g-at-f-at-5-minus-1)
  (implies
   (and
    (equal f-at-5
           (- (* 2 5) 3))
    (equal g-at-f-at-5-minus-1
           (+ (- f-at-5 1) 1)))
   (equal g-at-f-at-5-minus-1 7)))

(value-triple :itpeval-statement-checked)
:q
