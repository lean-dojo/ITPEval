;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_961:
;; the natural-number remainder of 2003 modulo 11 is 1.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-961-statement ()
  (equal (mod 2003 11) 1))

(value-triple :itpeval-statement-checked)
:q
