;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_462:
;; the exact arithmetic identity (1/2 + 1/3) * (1/2 - 1/3) = 5/36. This file
;; contains no proof.
;;
;; ACL2's exact rational arithmetic is faithful for this closed statement:
;; every term is rational, and the canonical embedding of the rationals into
;; the reals preserves and reflects the field operations and equality.

(in-package "ACL2")

(defun mathd-algebra-462-statement ()
  (equal (* (+ (/ 1 2)
               (/ 1 3))
            (- (/ 1 2)
               (/ 1 3)))
         (/ 5 36)))

(value-triple :itpeval-statement-checked)
:q
