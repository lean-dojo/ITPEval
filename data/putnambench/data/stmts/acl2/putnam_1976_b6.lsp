;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_b6:
;; every natural number whose sum of positive divisors is 2*N+1 is the square
;; of an odd integer. This file contains no proof.

(in-package "ACL2")

;; For positive n, every positive divisor is at most n, so this recursion sums
;; exactly all positive divisors. For n = 0 it gives the empty divisor sum.
(defun putnam-1976-b6-sum-divisors-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (and (natp n)
           (natp d))
      (if (zp d)
          0
        (+ (if (equal (mod n d) 0)
               d
             0)
           (putnam-1976-b6-sum-divisors-through
            n (- d 1))))
    0))

;; This bounded search is the internal existential odd square root. If an
;; integer m satisfies m^2 = n, its absolute value is a natural root at most n.
(defun putnam-1976-b6-odd-square-root-through-p (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (and (natp n)
           (natp candidate))
      (or (and (equal (mod candidate 2) 1)
               (equal (* candidate candidate) n))
          (and (not (zp candidate))
               (putnam-1976-b6-odd-square-root-through-p
                n (- candidate 1))))
    nil))

(defun putnambench-putnam-1976-b6-statement (n)
  (implies
   (and
    (natp n)
    (equal
     (putnam-1976-b6-sum-divisors-through n n)
     (+ (* 2 n) 1)))
   (putnam-1976-b6-odd-square-root-through-p n n)))

(value-triple :itpeval-statement-checked)
:q
