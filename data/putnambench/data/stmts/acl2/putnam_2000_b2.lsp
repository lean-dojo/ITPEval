;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_b2:
;; for all natural numbers 1 <= m <= n, n divides
;; gcd(m,n) * choose(n,m). This file contains no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-2000-b2-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-2000-b2-binomial-coefficient (- n 1) k)
       (putnam-2000-b2-binomial-coefficient
        (- n 1) (- k 1)))))

;; The subtraction Euclidean algorithm represents the natural-number gcd.
(defun putnam-2000-b2-gcd (m n)
  (declare (xargs :measure (+ (nfix m) (nfix n))))
  (if (and (natp m) (natp n))
      (cond
       ((equal m 0) n)
       ((equal n 0) m)
       ((<= m n)
        (putnam-2000-b2-gcd m (- n m)))
       (t
        (putnam-2000-b2-gcd (- m n) n)))
    0))

(defun putnambench-putnam-2000-b2-statement (m n)
  (implies
   (and
    (natp m)
    (natp n)
    (<= 1 m)
    (<= m n))
   (equal
    (mod
     (*
      (putnam-2000-b2-gcd m n)
      (putnam-2000-b2-binomial-coefficient n m))
     n)
    0)))

(value-triple :itpeval-statement-checked)
:q
