;; Statement-only formalization of miniF2F artifact mathd_numbertheory_335:
;; for every natural number n with remainder 5 modulo 7, five times n has
;; remainder 4 modulo 7. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-335-statement (n)
  (implies (and (natp n)
                (equal (mod n 7) 5))
           (equal (mod (* 5 n) 7) 4)))

(value-triple :itpeval-statement-checked)
:q
