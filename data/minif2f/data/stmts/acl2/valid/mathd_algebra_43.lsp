;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_43:
;; a real affine function f(x) = a*x + b with f(7) = 4 and f(6) = 3
;; satisfies f(3) = 0. This file contains no proof.
;;
;; Substituting the defining hypothesis eliminates the uniquely determined
;; function f. The two observation equations force a = 1 and b = -3, so every
;; satisfying real assignment is rational. Conversely, every guarded ACL2
;; assignment embeds unchanged into the reals with the displayed affine
;; function. Thus the rational guards and function elimination preserve the
;; source implication bidirectionally.

(in-package "ACL2")

(defun mathd-algebra-43-affine (x a b)
  (+ (* a x) b))

(defun mathd-algebra-43-statement (a b)
  (implies
   (and (rationalp a)
        (rationalp b)
        (equal (mathd-algebra-43-affine 7 a b) 4)
        (equal (mathd-algebra-43-affine 6 a b) 3))
   (equal (mathd-algebra-43-affine 3 a b) 0)))

(value-triple :itpeval-statement-checked)
:q
