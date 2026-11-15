;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_212:
;; the remainder of 16^17 * 17^18 * 18^19 modulo 10 is 8. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-212-statement ()
  (equal (mod (* (expt 16 17)
                 (expt 17 18)
                 (expt 18 19))
              10)
         8))

(value-triple :itpeval-statement-checked)
:q
