;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_728:
;; the difference 29^13 - 5^13 has remainder 3 modulo 7. This file contains
;; no proof.

(in-package "ACL2")

(defun mathd-numbertheory-728-statement ()
  (equal (mod (- (expt 29 13)
                 (expt 5 13))
              7)
         3))

(value-triple :itpeval-statement-checked)
:q
