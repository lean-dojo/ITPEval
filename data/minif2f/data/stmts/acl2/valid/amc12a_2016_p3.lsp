;; Statement-only formalization of miniF2F corpus artifact amc12a_2016_p3:
;; the floor-remainder formula x - y*floor(x/y), evaluated at x = 3/8 and
;; y = -2/5, equals -1/40. This file contains no proof.
;;
;; The source hypothesis fixes the function's value at every nonzero y, so
;; instantiating it at these arguments yields exactly the closed identity
;; below. Conversely, the displayed floor-remainder formula defines a source
;; function for nonzero y (with any value at y = 0), so eliminating the
;; universally quantified function is bidirectionally equivalent. ACL2's
;; exact rational arithmetic and two-argument floor preserve this evaluation.

(in-package "ACL2")

(defun amc12a-2016-p3-statement ()
  (equal (- (/ 3 8)
            (* (- (/ 2 5))
               (floor (/ 3 8) (- (/ 2 5)))))
         (- (/ 1 40))))

(value-triple :itpeval-statement-checked)
:q
