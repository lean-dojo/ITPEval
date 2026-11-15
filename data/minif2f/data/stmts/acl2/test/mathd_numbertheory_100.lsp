;; Statement-only formalization of miniF2F artifact mathd_numbertheory_100:
;; a positive natural number whose gcd with 40 is 10 and whose lcm with 40 is
;; 280 equals 70. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-100-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond ((equal a 0) b)
            ((equal b 0) a)
            ((< a b)
             (mathd-numbertheory-100-gcd a (- b a)))
            (t
             (mathd-numbertheory-100-gcd (- a b) b)))
    0))

(defun mathd-numbertheory-100-lcm (a b)
  (if (and (natp a) (natp b))
      (if (or (equal a 0) (equal b 0))
          0
        (/ (* a b) (mathd-numbertheory-100-gcd a b)))
    0))

(defun mathd-numbertheory-100-statement (n)
  (implies
   (and (natp n)
        (< 0 n)
        (equal (mathd-numbertheory-100-gcd n 40) 10)
        (equal (mathd-numbertheory-100-lcm n 40) 280))
   (equal n 70)))

(value-triple :itpeval-statement-checked)
:q
