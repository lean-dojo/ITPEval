;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_440:
;; over the real numbers, (3/2)/3 = x/10 implies x = 5. This file contains
;; no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here: the
;; equation forces x = 5, so every real solution is rational, while rational
;; solutions embed into the reals with the same equation and conclusion.

(in-package "ACL2")

(defun mathd-algebra-440-statement (x)
  (implies (and (rationalp x)
                (equal (/ (/ 3 2) 3)
                       (/ x 10)))
           (equal x 5)))

(value-triple :itpeval-statement-checked)
:q
