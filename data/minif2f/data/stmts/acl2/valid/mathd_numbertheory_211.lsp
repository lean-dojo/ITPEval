;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_211:
;; exactly 20 natural numbers below 60 have 4*n - 2 divisible by 6.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-211-solution-p (n)
  (and (natp n)
       (equal (mod (- (* 4 n) 2) 6) 0)))

(defun mathd-numbertheory-211-count-from (n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (if (mathd-numbertheory-211-solution-p n) 1 0)
       (mathd-numbertheory-211-count-from
        (+ n 1)
        (- remaining 1)))))

(defun mathd-numbertheory-211-statement ()
  (equal (mathd-numbertheory-211-count-from 0 60)
         20))

(value-triple :itpeval-statement-checked)
:q
