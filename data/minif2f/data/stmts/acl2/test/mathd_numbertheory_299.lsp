;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_299:
;; the product 1 * 3 * 5 * 7 * 9 * 11 * 13 has remainder 5 modulo 10.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-299-statement ()
  (equal (mod (* (* (* (* (* (* 1 3) 5) 7) 9) 11) 13)
              10)
         5))

(value-triple :itpeval-statement-checked)
:q
