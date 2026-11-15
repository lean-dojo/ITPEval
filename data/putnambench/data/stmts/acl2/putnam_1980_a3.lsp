;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_a3:
;; the integral from 0 to pi/2 of 1/(1+tan(x)^sqrt(2)) equals pi/4.
;; This file contains no proof.

(in-package "ACL2")

;; After x=(pi/2)u, the source equality is equivalent (because pi>0) to
;;
;;   integral_0^1 1/(1+tan(pi*u/2)^sqrt(2)) du = 1/2.
;;
;; The integrand on (0,1) extends continuously to the closed interval with
;; endpoint values 1 and 0, so its Lebesgue and Riemann integrals agree.
;; The functions below give an exact-rational diagonal approximation to that
;; normalized integral, rather than replacing the real integral by a fixed
;; finite quadrature.

(defun putnam-1980-a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1980-a3-factorial (- n 1)))))

;; With an even number of Leibniz summands this is a rational lower
;; approximation to pi, converging to pi as PRECISION tends to infinity.
(defun putnam-1980-a3-leibniz-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1980-a3-leibniz-prefix index)
         (/ sign (+ (* 2 index) 1))))))

(defun putnam-1980-a3-pi-lower (precision)
  (* 4
     (putnam-1980-a3-leibniz-prefix
      (* 2 (nfix precision)))))

;; Rational bisection lower approximation to the nonnegative square root of 2.
(defun putnam-1980-a3-sqrt-two-lower-aux
    (steps lower upper)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      lower
    (let ((midpoint (/ (+ lower upper) 2)))
      (if (<= (* midpoint midpoint) 2)
          (putnam-1980-a3-sqrt-two-lower-aux
           (- steps 1) midpoint upper)
        (putnam-1980-a3-sqrt-two-lower-aux
         (- steps 1) lower midpoint)))))

(defun putnam-1980-a3-sqrt-two-lower (steps)
  (putnam-1980-a3-sqrt-two-lower-aux
   steps 1 2))

;; Maclaurin prefixes for sine and cosine. All calls below use arguments in
;; [0,pi/2) and an odd number of summands.
(defun putnam-1980-a3-sine-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1980-a3-sine-prefix x index)
         (/ (* sign (expt x degree))
            (putnam-1980-a3-factorial degree))))))

(defun putnam-1980-a3-cosine-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (* 2 index))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1980-a3-cosine-prefix x index)
         (/ (* sign (expt x degree))
            (putnam-1980-a3-factorial degree))))))

(defun putnam-1980-a3-tangent-prefix
    (angle terms)
  (/ (putnam-1980-a3-sine-prefix angle terms)
     (putnam-1980-a3-cosine-prefix angle terms)))

;; For positive rational X, z=(X-1)/(X+1) has |z|<1 and
;;
;;   log(X) = 2*sum_(k>=0) z^(2k+1)/(2k+1).
(defun putnam-1980-a3-log-prefix-aux (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1)))
      (+ (putnam-1980-a3-log-prefix-aux z index)
         (/ (* 2 (expt z degree))
            degree)))))

(defun putnam-1980-a3-log-prefix (x terms)
  (if (and (rationalp x)
           (< 0 x))
      (putnam-1980-a3-log-prefix-aux
       (/ (- x 1) (+ x 1))
       terms)
    0))

;; Maclaurin prefix for exp. The diagonal below uses an odd number of
;; summands, hence an even highest degree; this prefix is positive even for
;; negative arguments.
(defun putnam-1980-a3-exp-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((degree (- terms 1)))
      (+ (putnam-1980-a3-exp-prefix x degree)
         (/ (expt x degree)
            (putnam-1980-a3-factorial degree))))))

(defun putnam-1980-a3-fourth-power (n)
  (* n n n n))

(defun putnam-1980-a3-diagonal-terms (subdivisions)
  (+ 1
     (* 2
        (putnam-1980-a3-fourth-power
         subdivisions))))

(defun putnam-1980-a3-grid-integrand-prefix
    (index subdivisions)
  (if (and (posp subdivisions)
           (natp index)
           (< index subdivisions))
      (let* ((precision
              (putnam-1980-a3-fourth-power subdivisions))
             (series-terms
              (putnam-1980-a3-diagonal-terms subdivisions))
             (angle
              (* (/ index (* 2 subdivisions))
                 (putnam-1980-a3-pi-lower precision))))
        (if (zp index)
            1
          (let* ((tangent
                  (putnam-1980-a3-tangent-prefix
                   angle series-terms))
                 (log-tangent
                  (putnam-1980-a3-log-prefix
                   tangent precision))
                 (power
                  (putnam-1980-a3-exp-prefix
                   (* (putnam-1980-a3-sqrt-two-lower
                       subdivisions)
                      log-tangent)
                   series-terms)))
            (/ 1 (+ 1 power)))))
    0))

(defun putnam-1980-a3-riemann-sum-aux
    (index subdivisions)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (+ (putnam-1980-a3-grid-integrand-prefix
        index subdivisions)
       (putnam-1980-a3-riemann-sum-aux
        (- index 1) subdivisions))))

(defun putnam-1980-a3-riemann-sum (subdivisions)
  (if (posp subdivisions)
      (/ (putnam-1980-a3-riemann-sum-aux
          subdivisions subdivisions)
         subdivisions)
    0))

;; The normalized integrand is decreasing from 1 to 0, so its right Riemann
;; sums converge to its integral. On the selected diagonal, the rational
;; approximants to pi, sqrt(2), tan, log, and exp converge to the corresponding
;; real values as the subdivision count grows. The source integral identity
;; is stated through the plain epsilon definition of that joint limit. The
;; cutoff is existential; no numerical convergence rate is part of the
;; proposition.
(defun-sk putnam-1980-a3-tail-p (epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (< (abs
         (- (putnam-1980-a3-riemann-sum subdivisions)
            1/2))
        epsilon))))

(defun-sk putnam-1980-a3-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (putnam-1980-a3-tail-p epsilon cutoff))))

(defun putnambench-putnam-1980-a3-statement
    (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1980-a3-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
