;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_81:
;; the natural-number remainder of 71 modulo 3 is 2. This file contains no
;; proof.

(in-package "ACL2")

(defun mathd-numbertheory-81-statement ()
  (equal (mod 71 3) 2))

(value-triple :itpeval-statement-checked)
:q
