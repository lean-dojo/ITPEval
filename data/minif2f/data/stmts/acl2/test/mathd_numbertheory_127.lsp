;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_127: the sum of 2^k for natural numbers k from 0
;; through 100 has remainder 3 modulo 7. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-127-sum-below (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (mathd-numbertheory-127-sum-below (- n 1))
       (expt 2 (- n 1)))))

(defun mathd-numbertheory-127-statement ()
  (equal (mod (mathd-numbertheory-127-sum-below 101) 7)
         3))

(value-triple :itpeval-statement-checked)
:q
