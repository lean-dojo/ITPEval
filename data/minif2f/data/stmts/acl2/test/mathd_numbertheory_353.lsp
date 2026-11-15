;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_353: a natural number equal to the sum from 2010
;; through 4018 inclusive is divisible by 2009. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-353-sum-from (start remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ start
       (mathd-numbertheory-353-sum-from
        (+ start 1)
        (- remaining 1)))))

(defun mathd-numbertheory-353-statement (s)
  (implies
   (and (natp s)
        (equal s
               (mathd-numbertheory-353-sum-from 2010 2009)))
   (equal (mod s 2009) 0)))

(value-triple :itpeval-statement-checked)
:q
