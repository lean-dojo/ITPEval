;; Statement-only formalization of miniF2F artifact mathd_numbertheory_12:
;; exactly four natural numbers from 15 through 85 inclusive are divisible
;; by 20. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-12-count-divisible-from (n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (if (and (natp n)
                (equal (mod n 20) 0))
           1
         0)
       (mathd-numbertheory-12-count-divisible-from
        (+ n 1)
        (- remaining 1)))))

(defun mathd-numbertheory-12-statement ()
  (equal (mathd-numbertheory-12-count-divisible-from 15 71)
         4))

(value-triple :itpeval-statement-checked)
:q
