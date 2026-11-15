;; Statement-only formalization of PutnamBench artifact putnam_1969_b1:
;; if a positive natural number n has n+1 divisible by 24, then the sum of
;; all positive divisors of n is divisible by 24. This file contains no proof.

(in-package "ACL2")

;; For positive n, every natural divisor is positive and at most n. The
;; recursion therefore sums exactly the finite divisor set used in both
;; ground-truth statements.

(defun putnam-1969-b1-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (and (natp n)
           (natp d))
      (if (zp d)
          0
        (+ (if (equal (mod n d) 0)
               d
             0)
           (putnam-1969-b1-sum-divisors-through
            n (- d 1))))
    0))

(defun putnambench-putnam-1969-b1-statement (n)
  (implies
   (and
    (natp n)
    (< 0 n)
    (equal (mod (+ n 1) 24) 0))
   (equal
    (mod (putnam-1969-b1-sum-divisors-through n n) 24)
    0)))

(value-triple :itpeval-statement-checked)
:q
