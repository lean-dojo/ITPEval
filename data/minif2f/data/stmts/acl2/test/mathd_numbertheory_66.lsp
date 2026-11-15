;; Statement-only formalization of miniF2F artifact mathd_numbertheory_66:
;; the natural-number remainder of 194 modulo 11 is 7.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-66-statement ()
  (equal (mod 194 11) 7))

(value-triple :itpeval-statement-checked)
:q
