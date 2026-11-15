;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_269:
;; the natural-number remainder of 2005^2 + 2005^0 + 2005^0 + 2005^5
;; modulo 100 is 52. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-269-statement ()
  (equal
   (mod (+ (expt 2005 2)
           (expt 2005 0)
           (expt 2005 0)
           (expt 2005 5))
        100)
   52))

(value-triple :itpeval-statement-checked)
:q
