;; Statement-only formalization of miniF2F artifact mathd_numbertheory_198:
;; the natural-number remainder of 5^2005 modulo 100 is 25.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-198-statement ()
  (equal (mod (expt 5 2005) 100) 25))

(value-triple :itpeval-statement-checked)
:q
