;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_247:
;; every natural number n for which 3 times n has remainder 2 modulo 11 has
;; remainder 8 modulo 11. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-247-statement (n)
  (implies (and (natp n)
                (equal (mod (* 3 n) 11) 2))
           (equal (mod n 11) 8)))

(value-triple :itpeval-statement-checked)
:q
