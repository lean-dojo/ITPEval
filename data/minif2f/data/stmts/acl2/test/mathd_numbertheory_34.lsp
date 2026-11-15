;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_34: a natural number below 100 whose product with 9
;; has remainder 1 modulo 100 must equal 89. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-34-statement (x)
  (implies (and (natp x)
                (< x 100)
                (equal (mod (* x 9) 100) 1))
           (equal x 89)))

(value-triple :itpeval-statement-checked)
:q
