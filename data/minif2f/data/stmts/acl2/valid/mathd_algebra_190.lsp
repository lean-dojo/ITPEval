;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_190:
;; the exact arithmetic identity ((3/8 + 7/8) / (4/5)) = 25/16. This file
;; contains no proof.
;;
;; ACL2's exact rational arithmetic is faithful for this closed statement:
;; every term is rational, and equality is preserved and reflected by the
;; canonical embedding of the rationals into the reals.

(in-package "ACL2")

(defun mathd-algebra-190-statement ()
  (equal (/ (+ (/ 3 8)
               (/ 7 8))
            (/ 4 5))
         (/ 25 16)))

(value-triple :itpeval-statement-checked)
:q
