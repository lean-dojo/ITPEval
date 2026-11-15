;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_326:
;; for every integer n, if the product of n - 1, n, and n + 1 is 720, then
;; n + 1 is 10. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-326-statement (n)
  (implies
   (and (integerp n)
        (equal (* (- n 1) n (+ n 1)) 720))
   (equal (+ n 1) 10)))

(value-triple :itpeval-statement-checked)
:q
