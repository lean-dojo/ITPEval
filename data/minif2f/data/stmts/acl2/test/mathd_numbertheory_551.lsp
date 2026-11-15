;; Statement-only formalization of miniF2F artifact mathd_numbertheory_551:
;; the natural-number remainder of 1529 modulo 6 is 5.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-551-statement ()
  (equal (mod 1529 6) 5))

(value-triple :itpeval-statement-checked)
:q
