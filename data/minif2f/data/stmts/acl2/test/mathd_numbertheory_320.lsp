;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_320:
;; a natural number below 101 whose difference from 123456 is divisible by 101
;; must equal 34. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-320-statement (n)
  (implies (and (natp n)
                (< n 101)
                (equal (mod (- 123456 n) 101) 0))
           (equal n 34)))

(value-triple :itpeval-statement-checked)
:q
