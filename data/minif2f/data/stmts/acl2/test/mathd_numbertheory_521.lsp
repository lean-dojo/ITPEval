;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_521:
;; even natural numbers m and n with difference m - n equal to 2 and product
;; m*n equal to 288 must have m equal to 18. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-521-statement (m n)
  (implies
   (and (natp m)
        (natp n)
        (equal (mod m 2) 0)
        (equal (mod n 2) 0)
        (equal (- m n) 2)
        (equal (* m n) 288))
   (equal m 18)))

(value-triple :itpeval-statement-checked)
:q
