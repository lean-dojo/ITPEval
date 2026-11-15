;; Statement-only formalization of miniF2F artifact mathd_algebra_10: over the
;; real numbers, the absolute value of (120/100) * 30 - (130/100) * 20 is 10.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-10-statement ()
  (equal (abs (- (* (/ 120 100) 30)
                 (* (/ 130 100) 20)))
         10))

(value-triple :itpeval-statement-checked)
:q
