;; Statement-only formalization of miniF2F artifact mathd_numbertheory_185:
;; every natural number congruent to 3 modulo 5 has twice its value congruent
;; to 1 modulo 5. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-185-statement (n)
  (implies (and (natp n)
                (equal (mod n 5) 3))
           (equal (mod (* 2 n) 5) 1)))

(value-triple :itpeval-statement-checked)
:q
