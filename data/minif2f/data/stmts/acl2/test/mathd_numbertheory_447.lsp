;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_447: the sum of the residues modulo 10 of natural
;; multiples of 3 from 1 through 49 is 78. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-447-sum (k remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (if (equal (mod k 3) 0)
           (mod k 10)
         0)
       (mathd-numbertheory-447-sum
        (+ k 1)
        (- remaining 1)))))

(defun mathd-numbertheory-447-statement ()
  (equal (mathd-numbertheory-447-sum 1 49)
         78))

(value-triple :itpeval-statement-checked)
:q
