;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_85:
;; the natural-number base-3 expression 1*3^3 + 2*3^2 + 2*3 + 2 equals 53.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-85-statement ()
  (equal (+ (* 1 (expt 3 3))
            (* 2 (expt 3 2))
            (* 2 3)
            2)
         53))

(value-triple :itpeval-statement-checked)
:q
