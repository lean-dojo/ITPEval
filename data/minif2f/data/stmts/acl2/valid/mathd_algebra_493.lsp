;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_493:
;; the real function f(x) = x^2 - 4*sqrt(x) + 1 satisfies f(f(4)) = 70.
;; This file contains no proof.
;;
;; The source pointwise hypothesis uniquely determines f, so eliminating the
;; universally quantified function leaves the same closed nested evaluation.
;; Its first argument is 4, whose principal real square root is 2, giving
;; f(4) = 9; the next principal square root is therefore 3. These values are
;; exact rationals in ACL2, and the nonnegative-square equations below are
;; bidirectionally equivalent to the two principal-square-root evaluations.
;; No free real variable or function domain is restricted by this elimination.

(in-package "ACL2")

(defun mathd-algebra-493-principal-square-root-value-p (root radicand)
  (and (rationalp root)
       (rationalp radicand)
       (<= 0 root)
       (equal (expt root 2) radicand)))

(defun mathd-algebra-493-formula-value (x square-root-x)
  (+ (expt x 2)
     (- (* 4 square-root-x))
     1))

(defun mathd-algebra-493-statement ()
  (let* ((sqrt-four 2)
         (f-at-four
          (mathd-algebra-493-formula-value 4 sqrt-four))
         (sqrt-f-at-four 3)
         (f-at-f-at-four
          (mathd-algebra-493-formula-value
           f-at-four
           sqrt-f-at-four)))
    (and
     (mathd-algebra-493-principal-square-root-value-p
      sqrt-four 4)
     (mathd-algebra-493-principal-square-root-value-p
      sqrt-f-at-four f-at-four)
     (equal f-at-f-at-four 70))))

(value-triple :itpeval-statement-checked)
:q
