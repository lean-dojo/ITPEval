;; Statement-only formalization of miniF2F artifact mathd_algebra_263: for a
;; real number y, if 19 + 3*y is nonnegative and has principal square root 7,
;; then y = 10. This file contains no proof.

(in-package "ACL2")

;; For a nonnegative real radicand, having principal square root 7 is
;; equivalent to being equal to 7^2. The resulting equation
;; 19 + 3*y = 49 forces the unique real value y = 10, so every satisfying
;; source assignment is rational; conversely, y = 10 satisfies both source
;; hypotheses. Thus the rational ACL2 encoding preserves the full real
;; satisfying locus in both directions.
(defun mathd-algebra-263-statement (y)
  (let ((radicand (+ 19 (* 3 y))))
    (implies (and (rationalp y)
                  (<= 0 radicand)
                  (equal radicand (expt 7 2)))
             (equal y 10))))

(value-triple :itpeval-statement-checked)
:q
