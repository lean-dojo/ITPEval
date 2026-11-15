;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_a2:
;; for every nonnegative integer k, the finite binomial sum from j = 0
;; through k of 2^(k-j) * choose(k+j,j) equals 4^k. This file contains no
;; proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-2020-a2-binomial-coefficient (n j)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (and (natp n) (natp j))) 0)
   ((equal j 0) 1)
   ((< n j) 0)
   ((equal n 0) 0)
   (t
    (+ (putnam-2020-a2-binomial-coefficient
        (- n 1) (- j 1))
       (putnam-2020-a2-binomial-coefficient
        (- n 1) j)))))

;; This is the inclusive sum from j = 0 through upper. In the statement,
;; upper = k, so every exponent k-j is a natural number.
(defun putnam-2020-a2-sum-through (k upper)
  (declare (xargs :measure (nfix upper)))
  (let ((term
         (* (expt 2 (- k upper))
            (putnam-2020-a2-binomial-coefficient
             (+ k upper) upper))))
    (if (zp upper)
        term
      (+ (putnam-2020-a2-sum-through
          k (- upper 1))
         term))))

(defun putnam-2020-a2-solution (k)
  (expt 4 k))

(defun putnambench-putnam-2020-a2-statement (k)
  (implies
   (natp k)
   (equal
    (putnam-2020-a2-sum-through k k)
    (putnam-2020-a2-solution k))))

(value-triple :itpeval-statement-checked)
:q
