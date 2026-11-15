;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_156:
;; for every positive natural number n, the greatest common divisor of n + 7
;; and 2*n + 1 is at most 13. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-156-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-156-gcd a (- b a)))
            (t
             (mathd-numbertheory-156-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-156-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (<= (mathd-numbertheory-156-gcd
        (+ n 7)
        (+ (* 2 n) 1))
       13)))

(value-triple :itpeval-statement-checked)
:q
