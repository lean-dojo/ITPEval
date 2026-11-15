;; Statement-only formalization of miniF2F artifact mathd_numbertheory_101:
;; the natural-number remainder of 17 times 18 modulo 4 is 2.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-101-statement ()
  (equal (mod (* 17 18) 4) 2))

(value-triple :itpeval-statement-checked)
:q
