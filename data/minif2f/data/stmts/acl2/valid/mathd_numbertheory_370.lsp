;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_370:
;; every natural number n congruent to 3 modulo 7 makes 2*n + 1 divisible
;; by 7. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-370-statement (n)
  (implies (and (natp n)
                (equal (mod n 7) 3))
           (equal (mod (+ (* 2 n) 1) 7) 0)))

(value-triple :itpeval-statement-checked)
:q
