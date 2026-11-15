;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_237: the sum of the natural numbers from 0 through 100
;; has remainder 4 modulo 6. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-237-sum-below (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (mathd-numbertheory-237-sum-below (- n 1))
       (- n 1))))

(defun mathd-numbertheory-237-statement ()
  (equal (mod (mathd-numbertheory-237-sum-below 101) 6)
         4))

(value-triple :itpeval-statement-checked)
:q
