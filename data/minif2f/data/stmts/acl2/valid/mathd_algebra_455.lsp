;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_455:
;; a real number x satisfying 2 * (2 * (2 * (2 * x))) = 48 must equal 3.
;; This file contains no proof.
;;
;; The source equation is 16*x = 48, so every satisfying real x is 3 and
;; therefore rational. Conversely, each rational ACL2 assignment embeds
;; unchanged into the reals with the same equation and conclusion. Thus the
;; rational guard is bidirectionally validity-equivalent to the real sources;
;; it also includes the Rocq source's natural-number specialization.

(in-package "ACL2")

(defun mathd-algebra-455-statement (x)
  (implies
   (and (rationalp x)
        (equal (* 2 (* 2 (* 2 (* 2 x))))
               48))
   (equal x 3)))

(value-triple :itpeval-statement-checked)
:q
