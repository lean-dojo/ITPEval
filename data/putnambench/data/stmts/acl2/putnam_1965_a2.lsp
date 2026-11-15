;; Statement-only formalization of PutnamBench artifact putnam_1965_a2:
;; for every positive natural n, a finite sum of squared rational terms
;; involving choose(n,r) equals choose(2n-2,n-1)/n. This file contains no
;; proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1965-a2-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1965-a2-binomial-coefficient (- n 1) k)
       (putnam-1965-a2-binomial-coefficient
        (- n 1) (- k 1)))))

;; This is the inclusive sum from r = 0 through upper. Under the statement
;; hypotheses, ACL2 division is exact rational division and upper is
;; floor((n-1)/2), so n - 2r is nonnegative throughout the sum.
(defun putnam-1965-a2-sum-through (n upper)
  (declare (xargs :measure (nfix upper)))
  (let ((term
         (expt
          (/ (* (- n (* 2 upper))
                (putnam-1965-a2-binomial-coefficient n upper))
             n)
          2)))
    (if (zp upper)
        term
      (+ (putnam-1965-a2-sum-through n (- upper 1))
         term))))

(defun putnambench-putnam-1965-a2-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-1965-a2-sum-through
     n (floor (- n 1) 2))
    (/ (putnam-1965-a2-binomial-coefficient
        (- (* 2 n) 2)
        (- n 1))
       n))))

(value-triple :itpeval-statement-checked)
:q
