;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_200:
;; 139 has remainder 7 when divided by 11. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-200-statement ()
  (equal (mod 139 11) 7))

(value-triple :itpeval-statement-checked)
:q
