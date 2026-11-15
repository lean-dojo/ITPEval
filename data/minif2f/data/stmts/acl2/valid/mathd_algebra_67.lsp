;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_67:
;; the real functions f(x) = 5*x + 3 and g(x) = x^2 - 2 satisfy
;; g(f(-1)) = 2. This file contains no proof.

(in-package "ACL2")

;; The two universal hypotheses uniquely define f and g, so substituting those
;; definitions into the conclusion gives the equivalent closed expression.
(defun mathd-algebra-67-statement ()
  (let* ((f-at-minus-one (+ (* 5 -1) 3))
         (g-at-f-at-minus-one
          (- (expt f-at-minus-one 2) 2)))
    (equal g-at-f-at-minus-one 2)))

(value-triple :itpeval-statement-checked)
:q
