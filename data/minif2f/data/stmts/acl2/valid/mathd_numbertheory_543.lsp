;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_543:
;; the number of positive natural-number divisors of 30^4, minus 2 in the
;; natural numbers, is 123. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-543-divisor-count-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod n d) 0)
           1
         0)
       (mathd-numbertheory-543-divisor-count-through n (- d 1)))))

(defun mathd-numbertheory-543-statement ()
  (let ((n (expt 30 4)))
    (equal
     (nfix
      (- (mathd-numbertheory-543-divisor-count-through n n)
         2))
     123)))

(value-triple :itpeval-statement-checked)
:q
