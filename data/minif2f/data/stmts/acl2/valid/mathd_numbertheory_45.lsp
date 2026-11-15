;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_45:
;; the natural-number greatest common divisor of 6432 and 132, increased by
;; 11, equals 23. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-45-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-45-gcd a (- b a)))
            (t
             (mathd-numbertheory-45-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-45-statement ()
  (equal (+ (mathd-numbertheory-45-gcd 6432 132) 11)
         23))

(value-triple :itpeval-statement-checked)
:q
