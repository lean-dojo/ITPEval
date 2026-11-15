;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_24:
;; the sum of 11^k for natural-number exponents k from 1 through 9 has
;; remainder 59 modulo 100. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-24-statement ()
  (equal
   (mod (+ (expt 11 1)
           (expt 11 2)
           (expt 11 3)
           (expt 11 4)
           (expt 11 5)
           (expt 11 6)
           (expt 11 7)
           (expt 11 8)
           (expt 11 9))
        100)
   59))

(value-triple :itpeval-statement-checked)
:q
