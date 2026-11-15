;; Statement-only formalization of miniF2F artifact mathd_numbertheory_175:
;; the natural-number remainder of 2 raised to the power 2010 modulo 10 is 4.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-175-statement ()
  (equal (mod (expt 2 2010) 10) 4))

(value-triple :itpeval-statement-checked)
:q
