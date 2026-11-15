;; Statement-only formalization of PutnamBench artifact putnam_1968_a1:
;; the identity equating 22/7 minus pi with the integral on [0,1] of
;; x^4(1-x)^4/(1+x^2). This file contains no proof.

(in-package "ACL2")

;; These exact rational prefixes converge to pi by Machin's identity
;; pi = 16*arctan(1/5) - 4*arctan(1/239).
(defun putnam-1968-a1-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (sign (if (equal (mod index 2) 0) 1 -1))
           (exponent (+ (* 2 index) 1)))
      (+ (putnam-1968-a1-arctan-prefix z index)
         (/ (* sign (expt z exponent))
            exponent)))))

(defun putnam-1968-a1-pi-prefix (terms)
  (- (* 16
        (putnam-1968-a1-arctan-prefix (/ 1 5) terms))
     (* 4
        (putnam-1968-a1-arctan-prefix (/ 1 239) terms))))

(defun putnam-1968-a1-integrand (x)
  (/ (* (expt x 4)
        (expt (- 1 x) 4))
     (+ 1 (expt x 2))))

;; The sum at SUBDIVISIONS is the right Riemann sum on the uniform partition
;; of [0,1]. Its values are exact rationals and its real limit is the source
;; integral.
(defun putnam-1968-a1-riemann-sum-aux (index subdivisions)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (+ (putnam-1968-a1-integrand
        (/ index subdivisions))
       (putnam-1968-a1-riemann-sum-aux
        (- index 1)
        subdivisions))))

(defun putnam-1968-a1-riemann-sum (subdivisions)
  (if (and (natp subdivisions)
           (< 0 subdivisions))
      (/ (putnam-1968-a1-riemann-sum-aux
          subdivisions
          subdivisions)
         subdivisions)
    0))

;; For epsilon = p/q > 0, 40q controls both approximation errors. The
;; alternating-series error of the pi prefix is below 1/(4q), while the
;; integrand is 10-Lipschitz on [0,1], so the Riemann-sum error is at most
;; 5/(40q). Thus using this fixed modulus is equivalent to equality of the
;; two represented real limits, rather than a bounded approximation.
(defun putnam-1968-a1-cutoff (epsilon)
  (if (and (rationalp epsilon)
           (< 0 epsilon))
      (* 40 (denominator epsilon))
    0))

(defun putnambench-putnam-1968-a1-statement
    (epsilon pi-terms subdivisions)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon)
        (natp pi-terms)
        (<= (putnam-1968-a1-cutoff epsilon)
            pi-terms)
        (natp subdivisions)
        (<= (putnam-1968-a1-cutoff epsilon)
            subdivisions))
   (< (abs
       (- (- (/ 22 7)
             (putnam-1968-a1-pi-prefix pi-terms))
          (putnam-1968-a1-riemann-sum subdivisions)))
      epsilon)))

(value-triple :itpeval-statement-checked)
:q
