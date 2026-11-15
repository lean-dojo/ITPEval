;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_328:
;; the natural-number remainder of 5 raised to the power 999999 modulo 7 is 6.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-328-statement ()
  (equal (mod (expt 5 999999) 7) 6))

(value-triple :itpeval-statement-checked)
:q
