;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_149: the sum of the natural numbers below 50 that
;; have remainder 5 modulo 8 and remainder 3 modulo 6 is 66.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-149-filtered-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let ((k (- n 1)))
      (+ (mathd-numbertheory-149-filtered-sum k)
         (if (and (equal (mod k 8) 5)
                  (equal (mod k 6) 3))
             k
           0)))))

(defun mathd-numbertheory-149-statement ()
  (equal (mathd-numbertheory-149-filtered-sum 50)
         66))

(value-triple :itpeval-statement-checked)
:q
