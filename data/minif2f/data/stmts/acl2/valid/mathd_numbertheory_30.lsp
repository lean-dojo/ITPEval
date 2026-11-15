;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_30:
;; the sum of the squares of 33818 through 33822 has natural-number remainder
;; zero modulo 17. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-30-statement ()
  (equal
   (mod (+ (expt 33818 2)
           (expt 33819 2)
           (expt 33820 2)
           (expt 33821 2)
           (expt 33822 2))
        17)
   0))

(value-triple :itpeval-statement-checked)
:q
