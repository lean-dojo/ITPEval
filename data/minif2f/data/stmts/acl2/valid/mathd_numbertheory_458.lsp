;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_458:
;; every natural number congruent to 7 modulo 8 is congruent to 3 modulo 4.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-458-statement (n)
  (implies
   (and (natp n)
        (equal (mod n 8) 7))
   (equal (mod n 4) 3)))

(value-triple :itpeval-statement-checked)
:q
