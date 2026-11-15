;; Statement-only formalization of PutnamBench corpus artifact putnam_1975_b6:
;; two strict inequalities comparing harmonic sums with positive real roots
;; of consecutive natural numbers. This file contains no proof.

(in-package "ACL2")

(defun putnam-1975-b6-harmonic-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (putnam-1975-b6-harmonic-sum (- n 1))
       (/ 1 n))))

;; For n > 1, all quantities are positive, so strict monotonicity of the
;; nth power on the nonnegative reals makes
;;
;;   n*(n+1)^(1/n) < n+H_n
;;
;; equivalent to the exact rational inequality below.
(defun putnam-1975-b6-first-inequality-p (n)
  (< (+ n 1)
     (expt (/ (+ n (putnam-1975-b6-harmonic-sum n))
              n)
           n)))

;; For n > 2, writing m=n-1 and using n^(-1/m)=1/n^(1/m),
;;
;;   m*n^(-1/m) < n-H_n
;;
;; is equivalently m^m < n*(n-H_n)^m. This is the exponent -1/(n-1)
;; appearing in the Lean and Rocq statements and in the stated problem.
(defun putnam-1975-b6-second-inequality-p (n)
  (< (expt (- n 1) (- n 1))
     (* n
        (expt (- n (putnam-1975-b6-harmonic-sum n))
              (- n 1)))))

(defun putnambench-putnam-1975-b6-statement (n)
  (implies
   (natp n)
   (and
    (implies
     (< 1 n)
     (putnam-1975-b6-first-inequality-p n))
    (implies
     (< 2 n)
     (putnam-1975-b6-second-inequality-p n)))))

(value-triple :itpeval-statement-checked)
:q
