;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_247:
;; for real t and s and integer n = 3, if t = 2*s - s^2 and
;; s = n^2 - 2^n + 1, then t = 0. This file contains no proof.

(in-package "ACL2")

;; Under n = 3, the second equality fixes s at 2 and the first fixes t at 0.
;; Thus every satisfying source-real assignment lies in ACL2's exact rational
;; domain, while every encoded assignment embeds unchanged into the reals.
;; The source natural/integer variation for n also coincides under n = 3.
(defun mathd-algebra-247-statement (t-value s-value n)
  (implies
   (and (rationalp t-value)
        (rationalp s-value)
        (integerp n)
        (equal t-value (- (* 2 s-value) (* s-value s-value)))
        (equal s-value (+ (- (* n n) (expt 2 n)) 1))
        (equal n 3))
   (equal t-value 0)))

(value-triple :itpeval-statement-checked)
:q
