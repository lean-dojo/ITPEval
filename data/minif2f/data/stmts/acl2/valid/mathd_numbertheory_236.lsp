;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_236:
;; the natural number 1999^2000 has remainder 1 modulo 5. This file contains
;; no proof.

(in-package "ACL2")

(defun mathd-numbertheory-236-statement ()
  (equal (mod (expt 1999 2000) 5) 1))

(value-triple :itpeval-statement-checked)
:q
