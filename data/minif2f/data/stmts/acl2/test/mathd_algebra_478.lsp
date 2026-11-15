;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_478:
;; positive real b, h, and v satisfying v = (1/3)*(b*h), b = 30, and h = 13/2
;; have v = 65. This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here because
;; the hypotheses force b and h to the displayed rationals and then force v
;; to their rational product; hence every satisfying real tuple is rational.

(in-package "ACL2")

(defun mathd-algebra-478-statement (b h v)
  (implies
   (and (rationalp b)
        (rationalp h)
        (rationalp v)
        (< 0 b)
        (< 0 h)
        (< 0 v)
        (equal v (* (/ 1 3) (* b h)))
        (equal b 30)
        (equal h (/ 13 2)))
   (equal v 65)))

(value-triple :itpeval-statement-checked)
:q
