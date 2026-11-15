;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_92:
;; every natural number whose product with 5 has remainder 8 modulo 17 itself
;; has remainder 5 modulo 17. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-92-statement (n)
  (implies
   (and (natp n)
        (equal (mod (* 5 n) 17) 8))
   (equal (mod n 17) 5)))

(value-triple :itpeval-statement-checked)
:q
