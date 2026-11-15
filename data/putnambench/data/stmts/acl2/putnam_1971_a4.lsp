;; Statement-only formalization of PutnamBench artifact putnam_1971_a4:
;; for 0 < epsilon < 1, every coefficient in the homogeneous support of
;; (x+y)^n (x^2-(2-epsilon)xy+y^2) is strictly positive for all sufficiently
;; large n. This file contains no proof.

(in-package "ACL2")

;; Pascal recursion gives choose(n,k), with zero outside 0 <= k <= n.
(defun putnam-1971-a4-binomial (n k)
  (declare (xargs :measure (nfix n)))
  (if (and (natp n)
           (natp k)
           (<= k n))
      (if (or (zp k)
              (equal k n))
          1
        (+ (putnam-1971-a4-binomial (- n 1) (- k 1))
           (putnam-1971-a4-binomial (- n 1) k)))
    0))

;; This is the coefficient of x^i*y^(n+2-i) in the displayed polynomial.
(defun putnam-1971-a4-coefficient (n epsilon i)
  (+ (if (<= 2 i)
         (putnam-1971-a4-binomial n (- i 2))
       0)
     (- (* (- 2 epsilon)
           (if (<= 1 i)
               (putnam-1971-a4-binomial n (- i 1))
             0)))
     (putnam-1971-a4-binomial n i)))

(defun-sk putnam-1971-a4-all-coefficients-positive-p
    (epsilon n)
  (forall (i)
    (implies
     (and (natp i)
          (<= i (+ n 2)))
     (< 0
        (putnam-1971-a4-coefficient
         n epsilon i)))))

(defun-sk putnam-1971-a4-positive-tail-p
    (epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (putnam-1971-a4-all-coefficients-positive-p
      epsilon n))))

(defun-sk putnam-1971-a4-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1971-a4-positive-tail-p
      epsilon cutoff))))

;; Exact rational epsilon is bidirectionally equivalent here to arbitrary real
;; epsilon. Restriction gives one direction. Conversely, for a real epsilon
;; choose a positive rational q < epsilon. Every coefficient is
;; A-(2-epsilon)B+C with B a nonnegative binomial coefficient, so positivity
;; at q implies positivity at epsilon with the same cutoff.
(defun-sk putnambench-putnam-1971-a4-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon)
          (< epsilon 1))
     (putnam-1971-a4-cutoff-exists-p
      epsilon))))

(value-triple :itpeval-statement-checked)
:q
