;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_422:
;; for the real affine bijection sigma(t) = 5*t - 12, the equation
;; sigma(x + 1) = sigma^{-1}(x) implies x = 47/24. This file contains no proof.
;;
;; The defining formula uniquely determines sigma and its inverse:
;; sigma^{-1}(x) = (x + 12)/5. Hence the source hypothesis is exactly the
;; equation encoded below. That equation forces 24*x = 47, so every satisfying
;; real x is rational. Conversely, each guarded ACL2 assignment embeds
;; unchanged into the reals with the stated affine bijection. Thus the
;; rational guard omits no source instance.

(in-package "ACL2")

(defun mathd-algebra-422-statement (x)
  (implies
   (and
    (rationalp x)
    (equal (- (* 5 (+ x 1)) 12)
           (/ (+ x 12) 5)))
   (equal x (/ 47 24))))

(value-triple :itpeval-statement-checked)
:q
