;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_a4:
;; for positive natural k with m = 6*k - 1, the alternating binomial sum
;; over j = 1,...,2*k - 1 is nonzero. This file contains no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1983-a4-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1983-a4-binomial-coefficient (- n 1) k)
       (putnam-1983-a4-binomial-coefficient
        (- n 1) (- k 1)))))

;; Sum (-1)^(j+1) * choose(m,3*j-1) for j = 1,...,upper.
(defun putnam-1983-a4-alternating-binomial-sum (m upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (putnam-1983-a4-alternating-binomial-sum
        m (- upper 1))
       (* (expt -1 (+ upper 1))
          (putnam-1983-a4-binomial-coefficient
           m (- (* 3 upper) 1))))))

(defun putnambench-putnam-1983-a4-statement (k m s)
  (implies
   (and (natp k)
        (< 0 k)
        (natp m)
        (integerp s)
        (equal m (- (* 6 k) 1))
        (equal
         s
         (putnam-1983-a4-alternating-binomial-sum
          m (- (* 2 k) 1))))
   (not (equal s 0))))

(value-triple :itpeval-statement-checked)
:q
