;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_403:
;; the sum of all positive proper natural-number divisors of 198 is 270. This
;; file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-403-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod n d) 0)
           d
         0)
       (mathd-numbertheory-403-sum-divisors-through n (- d 1)))))

(defun mathd-numbertheory-403-statement ()
  (equal (mathd-numbertheory-403-sum-divisors-through 198 197)
         270))

(value-triple :itpeval-statement-checked)
:q
