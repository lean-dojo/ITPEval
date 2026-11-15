;; Statement-only formalization of miniF2F artifact mathd_algebra_33: real
;; numbers x, y, and z with nonzero x, linked by 2*x = 5*y and 7*y = 10*z,
;; satisfy z/x = 7/25.
;; This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here. Every
;; rational counterexample is a real counterexample. Conversely, dividing any
;; real counterexample by its nonzero x-coordinate preserves both homogeneous
;; equations and the failed ratio conclusion. The normalized tuple
;; (1, y/x, z/x) is rational because the equations express its last two
;; coordinates as rational multiples. Thus no irrational counterexample is
;; omitted by the guarded ACL2 statement.

(in-package "ACL2")

(defun mathd-algebra-33-statement (x y z)
  (implies
   (and (rationalp x)
        (rationalp y)
        (rationalp z)
        (not (equal x 0))
        (equal (* 2 x) (* 5 y))
        (equal (* 7 y) (* 10 z)))
   (equal (/ z x) (/ 7 25))))

(value-triple :itpeval-statement-checked)
:q
