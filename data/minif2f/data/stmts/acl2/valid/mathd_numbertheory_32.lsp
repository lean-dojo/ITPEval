;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_32:
;; the sum of all positive natural-number divisors of 36 is 91. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-32-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod n d) 0)
           d
         0)
       (mathd-numbertheory-32-sum-divisors-through n (- d 1)))))

(defun mathd-numbertheory-32-statement ()
  (equal (mathd-numbertheory-32-sum-divisors-through 36 36)
         91))

(value-triple :itpeval-statement-checked)
:q
