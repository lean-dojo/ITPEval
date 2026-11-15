;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_33:
;; every natural number below 398 whose product with 7 has remainder 1 modulo
;; 398 equals 57. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-33-statement (n)
  (implies (and (natp n)
                (< n 398)
                (equal (mod (* n 7) 398) 1))
           (equal n 57)))

(value-triple :itpeval-statement-checked)
:q
