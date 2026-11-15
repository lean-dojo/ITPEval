;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_a1:
;; the exponent of 5 in 1^1*2^2*...*n^n, divided by n^2, tends to 1/8.
;; This file contains no proof.

(in-package "ACL2")

;; V5-AUX computes the exponent of 5 in a positive integer.  The fuel is
;; initialized to the integer itself, which exceeds the number of successive
;; divisions by 5, so it does not bound or approximate the valuation.
(defun putnam-1981-a1-v5-aux (value fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      0
    (if (and (posp value)
             (equal (mod value 5) 0))
        (+ 1
           (putnam-1981-a1-v5-aux
            (floor value 5)
            (- fuel 1)))
      0)))

(defun putnam-1981-a1-v5 (value)
  (if (posp value)
      (putnam-1981-a1-v5-aux value value)
    0))

;; Additivity of prime valuations gives
;;   v_5(product_(m=1)^n m^m) = sum_(m=1)^n m*v_5(m).
;; Thus this is exactly the greatest k for which 5^k divides the source
;; product, rather than a replacement sequence.
(defun putnam-1981-a1-exponent (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (putnam-1981-a1-exponent (- n 1))
       (* n (putnam-1981-a1-v5 n)))))

(defun putnam-1981-a1-normalized-exponent (n)
  (if (posp n)
      (/ (putnam-1981-a1-exponent n)
         (* n n))
    0))

;; Positive rational tolerances are cofinal in the positive reals, so this is
;; the epsilon definition of convergence to the real number 1/8.
(defun-sk putnam-1981-a1-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (< (abs
         (- (putnam-1981-a1-normalized-exponent n)
            1/8))
        epsilon))))

(defun-sk putnam-1981-a1-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1981-a1-tail-p epsilon cutoff))))

(defun putnambench-putnam-1981-a1-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1981-a1-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
