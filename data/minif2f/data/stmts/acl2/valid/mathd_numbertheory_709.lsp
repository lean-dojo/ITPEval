;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_709: a positive natural number n whose multiples 2*n
;; and 3*n have 28 and 30 positive divisors, respectively, has 6*n with
;; exactly 35 positive divisors. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-709-divisor-count-through (m d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod m d) 0)
           1
         0)
       (mathd-numbertheory-709-divisor-count-through
        m
        (- d 1)))))

(defun mathd-numbertheory-709-statement (n)
  (implies
   (and
    (natp n)
    (< 0 n)
    (equal
     (mathd-numbertheory-709-divisor-count-through
      (* 2 n)
      (* 2 n))
     28)
    (equal
     (mathd-numbertheory-709-divisor-count-through
      (* 3 n)
      (* 3 n))
     30))
   (equal
    (mathd-numbertheory-709-divisor-count-through
     (* 6 n)
     (* 6 n))
    35)))

(value-triple :itpeval-statement-checked)
:q
