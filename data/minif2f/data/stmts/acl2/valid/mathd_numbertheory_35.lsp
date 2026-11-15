;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_35:
;; the sum of all positive natural-number divisors of sqrt(196), namely 14,
;; is 24. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-35-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod n d) 0)
           d
         0)
       (mathd-numbertheory-35-sum-divisors-through n (- d 1)))))

(defun mathd-numbertheory-35-statement ()
  (equal (mathd-numbertheory-35-sum-divisors-through 14 14)
         24))

(value-triple :itpeval-statement-checked)
:q
