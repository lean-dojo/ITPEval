;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_239: the sum of the natural numbers from 1 through 12
;; has remainder 2 modulo 4. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-239-sum-to (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ n (mathd-numbertheory-239-sum-to (- n 1)))))

(defun mathd-numbertheory-239-statement ()
  (equal (mod (mathd-numbertheory-239-sum-to 12) 4)
         2))

(value-triple :itpeval-statement-checked)
:q
