;; Statement-only formalization of miniF2F artifact mathd_numbertheory_229:
;; the natural-number remainder of 5 raised to the 30th power modulo 7 is 1.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-229-statement ()
  (equal (mod (expt 5 30) 7) 1))

(value-triple :itpeval-statement-checked)
:q
