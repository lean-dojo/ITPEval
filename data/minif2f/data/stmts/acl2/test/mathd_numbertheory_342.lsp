;; Statement-only formalization of miniF2F artifact mathd_numbertheory_342:
;; the natural-number remainder of 54 modulo 6 is 0.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-342-statement ()
  (equal (mod 54 6) 0))

(value-triple :itpeval-statement-checked)
:q
