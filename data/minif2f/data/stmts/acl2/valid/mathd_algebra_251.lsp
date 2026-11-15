;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_251:
;; a nonzero real number x satisfying 3 + 1/x = 7/x must equal 2.
;; This file contains no proof.
;;
;; Standard ACL2 represents exact rationals rather than arbitrary reals, but
;; this predicate is bidirectionally equivalent to the source proposition.
;; The source hypotheses force x = 2, so every satisfying real assignment is
;; rational; conversely, each guarded ACL2 assignment embeds unchanged into
;; the reals.

(in-package "ACL2")

(defun mathd-algebra-251-statement (x)
  (implies
   (and (rationalp x)
        (not (equal x 0))
        (equal (+ 3 (/ 1 x))
               (/ 7 x)))
   (equal x 2)))

(value-triple :itpeval-statement-checked)
:q
