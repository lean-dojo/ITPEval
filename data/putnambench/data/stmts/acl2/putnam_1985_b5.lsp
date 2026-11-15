;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_b5:
;; the improper real integral of t^(-1/2)*exp(-1985*(t+t^(-1))) over the
;; positive half-line equals sqrt(pi/1985)*exp(-3970). This file contains no
;; proof.

(in-package "ACL2")

;; Standard ACL2 has exact rationals rather than primitive completed reals.
;; The definitions below give independent rational Cauchy names for the
;; source integral and its stated value. Under t=x^2, the source integral is
;;
;;   2 * integral_0^infinity exp(-1985*(x^2+x^(-2))) dx.
;;
;; Thus the expanding midpoint sums retain the original integrand through an
;; exact change of variables; they are not a fixed finite quadrature.

(defun putnam-1985-b5-exp-negative-approx (y scale)
  (if (and (rationalp y)
           (<= 0 y)
           (posp scale)
           (< y scale))
      (expt (- 1 (/ y scale)) scale)
    0))

(defun putnam-1985-b5-grid-point
    (index radius subdivisions)
  (let* ((lower (/ 1 radius))
         (width (- radius lower)))
    (+ lower
       (/ (* width (+ (* 2 index) 1))
          (* 2 subdivisions)))))

(defun putnam-1985-b5-integrand-approx
    (x scale)
  (if (and (rationalp x)
           (< 0 x))
      (* 2
         (putnam-1985-b5-exp-negative-approx
          (* 1985
             (+ (* x x)
                (/ 1 (* x x))))
          scale))
    0))

(defun putnam-1985-b5-midpoint-sum
    (remaining radius subdivisions scale)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- remaining 1))
           (x (putnam-1985-b5-grid-point
               index radius subdivisions)))
      (+ (putnam-1985-b5-integrand-approx x scale)
         (putnam-1985-b5-midpoint-sum
          index radius subdivisions scale)))))

(defun putnam-1985-b5-integral-approx
    (radius subdivisions scale)
  (if (and (posp radius)
           (posp subdivisions)
           (posp scale))
      (let ((width (- radius (/ 1 radius))))
        (* (/ width subdivisions)
           (putnam-1985-b5-midpoint-sum
            subdivisions radius subdivisions scale)))
    0))

;; Machin's identity gives
;;
;;   pi = 16*arctan(1/5) - 4*arctan(1/239).
;;
;; These alternating Taylor prefixes are exact rationals converging to pi.
(defun putnam-1985-b5-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1985-b5-arctan-prefix z index)
         (/ (* sign (expt z degree))
            degree)))))

(defun putnam-1985-b5-pi-prefix (terms)
  (- (* 16
        (putnam-1985-b5-arctan-prefix (/ 1 5) terms))
     (* 4
        (putnam-1985-b5-arctan-prefix (/ 1 239) terms))))

;; Rational bisection gives the nonnegative square root of the rational
;; Machin prefix divided by 1985. All relevant radicands lie between 0 and 1.
(defun putnam-1985-b5-sqrt-lower-aux
    (radicand steps lower upper)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      lower
    (let ((midpoint (/ (+ lower upper) 2)))
      (if (<= (* midpoint midpoint) radicand)
          (putnam-1985-b5-sqrt-lower-aux
           radicand (- steps 1) midpoint upper)
        (putnam-1985-b5-sqrt-lower-aux
         radicand (- steps 1) lower midpoint)))))

(defun putnam-1985-b5-sqrt-pi-over-1985-approx
    (pi-terms sqrt-steps)
  (putnam-1985-b5-sqrt-lower-aux
   (/ (putnam-1985-b5-pi-prefix pi-terms) 1985)
   sqrt-steps
   0
   1))

(defun putnam-1985-b5-solution-approx
    (scale pi-terms sqrt-steps)
  (* (putnam-1985-b5-sqrt-pi-over-1985-approx
      pi-terms sqrt-steps)
     (putnam-1985-b5-exp-negative-approx 3970 scale)))

;; This is the directed-limit statement itself, without imposing a particular
;; convergence rate. For each tolerance there is an outer radius after which,
;; for each fixed radius, sufficiently accurate quadrature, exponential, pi,
;; and square-root approximations agree to that tolerance. Allowing the inner
;; cutoffs to depend on the radius is essential for the improper integral.

(defun-sk putnam-1985-b5-all-precisions-close-p
    (epsilon radius subdivisions-cutoff scale-cutoff
             pi-terms-cutoff sqrt-steps-cutoff)
  (forall (subdivisions scale pi-terms sqrt-steps)
    (implies
     (and
      (natp subdivisions)
      (<= subdivisions-cutoff subdivisions)
      (natp scale)
      (<= scale-cutoff scale)
      (natp pi-terms)
      (<= pi-terms-cutoff pi-terms)
      (natp sqrt-steps)
      (<= sqrt-steps-cutoff sqrt-steps))
     (< (abs
         (- (putnam-1985-b5-integral-approx
             radius subdivisions scale)
            (putnam-1985-b5-solution-approx
             scale pi-terms sqrt-steps)))
        epsilon))))

(defun-sk putnam-1985-b5-precision-cutoffs-exist-p
    (epsilon radius)
  (exists
   (subdivisions-cutoff scale-cutoff
                        pi-terms-cutoff sqrt-steps-cutoff)
   (and
    (posp subdivisions-cutoff)
    (posp scale-cutoff)
    (posp pi-terms-cutoff)
    (posp sqrt-steps-cutoff)
    (putnam-1985-b5-all-precisions-close-p
     epsilon radius subdivisions-cutoff scale-cutoff
     pi-terms-cutoff sqrt-steps-cutoff))))

(defun-sk putnam-1985-b5-radius-tail-p
    (epsilon radius-cutoff)
  (forall (radius)
    (implies
     (and
      (natp radius)
      (<= radius-cutoff radius))
     (putnam-1985-b5-precision-cutoffs-exist-p
      epsilon radius))))

(defun-sk putnam-1985-b5-radius-cutoff-exists-p (epsilon)
  (exists (radius-cutoff)
    (and
     (posp radius-cutoff)
     (putnam-1985-b5-radius-tail-p
      epsilon radius-cutoff))))

(defun putnambench-putnam-1985-b5-statement (epsilon)
  (implies
   (and
    (rationalp epsilon)
    (< 0 epsilon))
   (putnam-1985-b5-radius-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
