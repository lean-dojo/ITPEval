;; Statement-only formalization of PutnamBench artifact putnam_1962_a5:
;; the natural-number closed form for the sum from k = 1 through n of
;; choose(n,k) * k^2. This file contains no proof.

(in-package "ACL2")

;; Pascal's recurrence is Nat.choose, the recursive sum enumerates exactly
;; k = 1,...,n, and nfix represents truncated natural-number subtraction.
(defun putnam-1962-a5-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1962-a5-binomial-coefficient (- n 1) k)
       (putnam-1962-a5-binomial-coefficient
        (- n 1) (- k 1)))))

(defun putnam-1962-a5-binomial-square-sum-through (n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      0
    (+ (putnam-1962-a5-binomial-square-sum-through
        n (- k 1))
       (* (putnam-1962-a5-binomial-coefficient n k)
          (* k k)))))

(defun putnam-1962-a5-solution (n)
  (* n
     (* (+ n 1)
        (expt 2 (nfix (- n 2))))))

(defun putnambench-putnam-1962-a5-statement (n)
  (implies
   (and (natp n)
        (>= n 2))
   (equal
    (putnam-1962-a5-solution n)
    (putnam-1962-a5-binomial-square-sum-through n n))))

(value-triple :itpeval-statement-checked)
:q
