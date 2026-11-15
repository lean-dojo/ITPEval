;; Statement-only formalization of miniF2F artifact mathd_algebra_276: integer
;; factors whose product is the real polynomial 10*x^2 - x - 24 satisfy
;; a*b + b = 12. This file contains no proof.
;;
;; Expanding (a*x - 8)*(b*x + 3) gives coefficients a*b, 3*a - 8*b,
;; and -24. Hence its equality to 10*x^2 - x - 24 for every real x is
;; bidirectionally equivalent to the two nonconstant coefficient equations
;; below; the constant coefficients already coincide.

(in-package "ACL2")

(defun mathd-algebra-276-statement (a b)
  (implies
   (and (integerp a)
        (integerp b)
        (equal (* a b) 10)
        (equal (- (* 3 a) (* 8 b)) -1))
   (equal (+ (* a b) b) 12)))

(value-triple :itpeval-statement-checked)
:q
