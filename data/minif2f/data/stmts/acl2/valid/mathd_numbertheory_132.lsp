;; Statement-only formalization of miniF2F artifact mathd_numbertheory_132:
;; the natural-number remainder of 2004 modulo 12 is 0. This file contains no
;; proof.

(in-package "ACL2")

(defun mathd-numbertheory-132-statement ()
  (equal (mod 2004 12) 0))

(value-triple :itpeval-statement-checked)
:q
