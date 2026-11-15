;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_221: exactly 11 positive natural numbers below 1000
;; have exactly three positive divisors. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-221-divisor-count-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod n d) 0) 1 0)
       (mathd-numbertheory-221-divisor-count-through
        n
        (- d 1)))))

(defun mathd-numbertheory-221-count-through (limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (+ (if (equal
             (mathd-numbertheory-221-divisor-count-through
              limit
              limit)
             3)
           1
         0)
       (mathd-numbertheory-221-count-through (- limit 1)))))

(defun mathd-numbertheory-221-statement ()
  (equal (mathd-numbertheory-221-count-through 999)
         11))

(value-triple :itpeval-statement-checked)
:q
