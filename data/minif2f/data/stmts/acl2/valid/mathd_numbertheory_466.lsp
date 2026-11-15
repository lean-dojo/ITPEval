;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_466:
;; the sum of the natural numbers below 11 has remainder 1 modulo 9. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-466-statement ()
  (equal
   (mod (+ 0 1 2 3 4 5 6 7 8 9 10)
        9)
   1))

(value-triple :itpeval-statement-checked)
:q
