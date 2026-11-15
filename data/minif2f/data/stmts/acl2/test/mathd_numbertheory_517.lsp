;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_517:
;; the natural-number remainder of 121 times 122 times 123 modulo 4 is 2.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-517-statement ()
  (equal (mod (* 121 122 123) 4) 2))

(value-triple :itpeval-statement-checked)
:q
