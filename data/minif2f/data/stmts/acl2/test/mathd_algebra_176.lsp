;; Statement-only formalization of miniF2F artifact mathd_algebra_176: the
;; real-number polynomial identity (x + 1)^2 * x = x^3 + 2 * x^2 + x. This
;; file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-176-statement (x)
  (implies (rationalp x)
           (equal (* (expt (+ x 1) 2) x)
                  (+ (+ (expt x 3)
                        (* 2 (expt x 2)))
                     x))))

(value-triple :itpeval-statement-checked)
:q
