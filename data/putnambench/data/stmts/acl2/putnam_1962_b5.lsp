;; Statement-only formalization of PutnamBench artifact putnam_1962_b5:
;; for every integer n greater than 1, the sum from i = 1 through n of
;; (i/n)^n lies strictly between (3n+1)/(2n+2) and 2. This file contains
;; no proof.

(in-package "ACL2")

;; Under n > 1, every base i/n is a positive rational and the integer
;; exponent n is natural. Thus ACL2's exact rational expt and order agree
;; with the corresponding real power and inequalities in the source.
(defun putnam-1962-b5-power-sum-through (n i)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      0
    (+ (putnam-1962-b5-power-sum-through n (- i 1))
       (expt (/ i n) n))))

(defun putnambench-putnam-1962-b5-statement (n)
  (implies
   (and (integerp n)
        (> n 1))
   (let ((power-sum
          (putnam-1962-b5-power-sum-through n n)))
     (and
      (< (/ (+ (* 3 n) 1)
            (+ (* 2 n) 2))
         power-sum)
      (< power-sum 2)))))

(value-triple :itpeval-statement-checked)
:q
