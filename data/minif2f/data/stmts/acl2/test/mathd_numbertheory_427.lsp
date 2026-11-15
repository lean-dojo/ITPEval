;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_427: if a natural number is the sum of the positive
;; divisors of 500, then the sum of its distinct prime divisors is 25.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-427-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod n d) 0) d 0)
       (mathd-numbertheory-427-sum-divisors-through n (- d 1)))))

(defun mathd-numbertheory-427-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (mathd-numbertheory-427-no-divisor-from-p n (+ d 1)))
    t))

(defun mathd-numbertheory-427-primep (n)
  (and (natp n)
       (< 1 n)
       (mathd-numbertheory-427-no-divisor-from-p n 2)))

(defun mathd-numbertheory-427-sum-prime-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (and (mathd-numbertheory-427-primep d)
                (equal (mod n d) 0))
           d
         0)
       (mathd-numbertheory-427-sum-prime-divisors-through
        n
        (- d 1)))))

(defun mathd-numbertheory-427-statement (a)
  (implies
   (and (natp a)
        (equal a
               (mathd-numbertheory-427-sum-divisors-through 500 500)))
   (equal (mathd-numbertheory-427-sum-prime-divisors-through a a)
          25)))

(value-triple :itpeval-statement-checked)
:q
