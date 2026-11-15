;; Statement-only formalization of miniF2F artifact mathd_numbertheory_314:
;; every positive natural number divisible by 1342 whose remainder modulo 13
;; is less than 1342 modulo 13 is at least 6710. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-314-statement (r n)
  (implies
   (and (natp r)
        (natp n)
        (equal r (mod 1342 13))
        (< 0 n)
        (equal (mod n 1342) 0)
        (< (mod n 13) r))
   (<= 6710 n)))

(value-triple :itpeval-statement-checked)
:q
