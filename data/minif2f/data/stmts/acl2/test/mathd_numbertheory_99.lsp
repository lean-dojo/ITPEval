;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_99:
;; every natural number n whose double has remainder 15 modulo 47 has
;; remainder 31 modulo 47. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-99-statement (n)
  (implies
   (and (natp n)
        (equal (mod (* 2 n) 47) 15))
   (equal (mod n 47) 31)))

(value-triple :itpeval-statement-checked)
:q
