;; Statement-only formalization of miniF2F artifact mathd_numbertheory_102:
;; the natural-number remainder of 2 raised to the eighth power modulo 5 is 1.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-102-statement ()
  (equal (mod (expt 2 8) 5) 1))

(value-triple :itpeval-statement-checked)
:q
