;; Statement-only formalization of miniF2F artifact mathd_algebra_432: for
;; every real x, (x + 3) * (2 * x - 6) equals 2 * x^2 - 18. ACL2's exact
;; rational encoding is bidirectionally equivalent here because this is a
;; universal identity between polynomials with rational coefficients. This
;; file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-432-statement (x)
  (implies (rationalp x)
           (equal (* (+ x 3)
                     (- (* 2 x) 6))
                  (- (* 2 (expt x 2)) 18))))

(value-triple :itpeval-statement-checked)
:q
