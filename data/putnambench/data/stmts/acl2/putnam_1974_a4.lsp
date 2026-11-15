;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_a4:
;; for every positive natural n, a normalized lower-half binomial sum equals
;; n times choose(n-1, floor(n/2)), with the same normalization.
;; This file contains no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1974-a4-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1974-a4-binomial-coefficient (- n 1) k)
       (putnam-1974-a4-binomial-coefficient
        (- n 1) (- k 1)))))

;; Sum (n - 2*k) * choose(n,k) for k = 0,...,term-count-1.
(defun putnam-1974-a4-lower-half-sum (n term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (let ((k (- term-count 1)))
      (+
       (* (- n (* 2 k))
          (putnam-1974-a4-binomial-coefficient n k))
       (putnam-1974-a4-lower-half-sum n k)))))

(defun putnambench-putnam-1974-a4-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (* (/ 1 (expt 2 (- n 1)))
       (putnam-1974-a4-lower-half-sum
        n (+ 1 (floor n 2))))
    (* (/ n (expt 2 (- n 1)))
       (putnam-1974-a4-binomial-coefficient
        (- n 1) (floor n 2))))))

(value-triple :itpeval-statement-checked)
:q
