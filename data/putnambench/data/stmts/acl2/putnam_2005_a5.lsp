;; Statement-only formalization of the PutnamBench corpus artifact
;; putnam_2005_a5: evaluation of the definite real integral on [0,1] of
;; log(1+x)/(1+x^2) as pi times log(2), divided by 8. This file contains no
;; proof.

(in-package "ACL2")

;; For positive rational X, Z=(X-1)/(X+1) has absolute value below 1, and
;;
;;   log(X) = 2 * sum_(k>=0) Z^(2k+1)/(2k+1).
;;
;; These exact rational prefixes are used both in the integrand and for
;; log(2) in the stated solution.
(defun putnam-2005-a5-log-prefix-aux (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1)))
      (+ (putnam-2005-a5-log-prefix-aux z index)
         (/ (* 2 (expt z degree))
            degree)))))

(defun putnam-2005-a5-log-prefix (x terms)
  (if (and (rationalp x)
           (< 0 x))
      (putnam-2005-a5-log-prefix-aux
       (/ (- x 1) (+ x 1))
       terms)
    0))

;; Exact rational Taylor prefixes for arctan(Z), used in Machin's identity
;;
;;   pi = 16*arctan(1/5) - 4*arctan(1/239).
(defun putnam-2005-a5-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-2005-a5-arctan-prefix z index)
         (/ (* sign (expt z degree))
            degree)))))

(defun putnam-2005-a5-pi-prefix (terms)
  (- (* 16
        (putnam-2005-a5-arctan-prefix (/ 1 5) terms))
     (* 4
        (putnam-2005-a5-arctan-prefix (/ 1 239) terms))))

(defun putnam-2005-a5-solution-approx
    (pi-terms solution-log-terms)
  (/ (* (putnam-2005-a5-pi-prefix pi-terms)
        (putnam-2005-a5-log-prefix 2 solution-log-terms))
     8))

;; The point REMAINING/SUBDIVISIONS ranges over the right endpoints of the
;; uniform partition of [0,1]. Every summand is exact rational arithmetic.
(defun putnam-2005-a5-integrand-approx
    (x integrand-log-terms)
  (/ (putnam-2005-a5-log-prefix
      (+ x 1) integrand-log-terms)
     (+ (* x x) 1)))

(defun putnam-2005-a5-riemann-sum-aux
    (remaining subdivisions integrand-log-terms)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-2005-a5-integrand-approx
        (/ remaining subdivisions)
        integrand-log-terms)
       (putnam-2005-a5-riemann-sum-aux
        (- remaining 1)
        subdivisions
        integrand-log-terms))))

(defun putnam-2005-a5-integral-approx
    (subdivisions integrand-log-terms)
  (if (posp subdivisions)
      (/ (putnam-2005-a5-riemann-sum-aux
          subdivisions subdivisions integrand-log-terms)
         subdivisions)
    0))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; The source asserts equality of two real limits, not a particular rate, so
;; each approximation modulus is existential and every later approximation
;; must remain inside the requested tolerance.

(defun-sk putnam-2005-a5-approximation-tail-p
    (epsilon subdivision-cutoff integrand-log-cutoff
             pi-cutoff solution-log-cutoff)
  (forall (subdivisions integrand-log-terms
                        pi-terms solution-log-terms)
    (implies
     (and
      (natp subdivisions)
      (<= subdivision-cutoff subdivisions)
      (natp integrand-log-terms)
      (<= integrand-log-cutoff integrand-log-terms)
      (natp pi-terms)
      (<= pi-cutoff pi-terms)
      (natp solution-log-terms)
      (<= solution-log-cutoff solution-log-terms))
     (< (abs
         (- (putnam-2005-a5-integral-approx
             subdivisions integrand-log-terms)
            (putnam-2005-a5-solution-approx
             pi-terms solution-log-terms)))
        epsilon))))

(defun-sk putnam-2005-a5-cutoffs-exist-p (epsilon)
  (exists (subdivision-cutoff integrand-log-cutoff
                              pi-cutoff solution-log-cutoff)
    (and
     (posp subdivision-cutoff)
     (posp integrand-log-cutoff)
     (posp pi-cutoff)
     (posp solution-log-cutoff)
     (putnam-2005-a5-approximation-tail-p
      epsilon subdivision-cutoff integrand-log-cutoff
      pi-cutoff solution-log-cutoff))))

(defun-sk putnambench-putnam-2005-a5-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2005-a5-cutoffs-exist-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
