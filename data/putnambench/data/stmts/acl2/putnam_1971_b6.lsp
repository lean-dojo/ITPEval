;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_b6:
;; for every positive integer x, the sum from 1 through x of the greatest odd
;; divisor of n divided by n differs from 2*x/3 by less than 1 in absolute
;; value. This file contains no proof.

(in-package "ACL2")

;; For positive n, every positive divisor is at most n. Descending from n
;; therefore returns exactly the greatest odd divisor, with 1 as the final
;; possible candidate.
(defun putnam-1971-b6-greatest-odd-divisor-through (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (and (natp n)
           (natp candidate))
      (if (zp candidate)
          1
        (if (and (equal (mod n candidate) 0)
                 (equal (mod candidate 2) 1))
            candidate
          (putnam-1971-b6-greatest-odd-divisor-through
           n (- candidate 1))))
    0))

(defun putnam-1971-b6-greatest-odd-divisor (n)
  (if (and (natp n)
           (< 0 n))
      (putnam-1971-b6-greatest-odd-divisor-through n n)
    0))

;; This is the exact rational sum of delta(n)/n for n = 1 through x.
(defun putnam-1971-b6-sum-through (x)
  (declare (xargs :measure (nfix x)))
  (if (natp x)
      (if (zp x)
          0
        (+ (putnam-1971-b6-sum-through (- x 1))
           (/ (putnam-1971-b6-greatest-odd-divisor x)
              x)))
    0))

(defun putnambench-putnam-1971-b6-statement (x)
  (implies
   (and (natp x)
        (< 0 x))
   (< (abs
       (- (putnam-1971-b6-sum-through x)
          (/ (* 2 x) 3)))
      1)))

(value-triple :itpeval-statement-checked)
:q
