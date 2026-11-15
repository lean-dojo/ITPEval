;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_84:
;; the floor of 9 divided by 160, multiplied by 100, is 5. This file contains
;; no proof.

(in-package "ACL2")

(defun mathd-numbertheory-84-statement ()
  (equal (floor (* (/ 9 160) 100) 1)
         5))

(value-triple :itpeval-statement-checked)
:q
