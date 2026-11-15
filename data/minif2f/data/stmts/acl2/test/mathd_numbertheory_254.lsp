;; Statement-only formalization of miniF2F artifact mathd_numbertheory_254:
;; the sum 239 + 174 + 83 has remainder 6 modulo 10.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-254-statement ()
  (equal (mod (+ (+ 239 174) 83) 10)
         6))

(value-triple :itpeval-statement-checked)
:q
