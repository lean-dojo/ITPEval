;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_321:
;; the canonical residue modulo 1399 whose product with 160 has remainder 1 is
;; 1058. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-321-statement (n)
  (implies (and (integerp n)
                (<= 0 n)
                (< n 1399)
                (equal (mod (* n 160) 1399) 1))
           (equal n 1058)))

(value-triple :itpeval-statement-checked)
:q
