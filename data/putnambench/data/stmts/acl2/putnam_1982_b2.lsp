;; Statement-only formalization of PutnamBench corpus artifact putnam_1982_b2:
;; the Gaussian integral of the integer-lattice point count in a centered
;; disk equals pi times the square of twice a Gaussian series minus one.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has exact rationals but no primitive completed real field.
;; The functions below are rational approximants used inside an unbounded
;; limit definition.  The source variables A, g, and I are uniquely fixed by
;; their defining hypotheses, so they are eliminated definitionally.

;; For 0 <= T < SCALE, (1-T/SCALE)^SCALE converges upward to exp(-T).
(defun putnam-1982-b2-gaussian-approx (t-value scale)
  (if (and (rationalp t-value)
           (<= 0 t-value)
           (natp scale)
           (< 0 scale)
           (< t-value scale))
      (expt (- 1 (/ t-value scale)) scale)
    0))

;; With TERMS summands, this is four times the corresponding Leibniz prefix
;; for pi.  Every value is rational and the prefixes converge to pi.
(defun putnam-1982-b2-leibniz-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1982-b2-leibniz-prefix index)
         (/ sign (+ (* 2 index) 1))))))

(defun putnam-1982-b2-pi-prefix (terms)
  (* 4 (putnam-1982-b2-leibniz-prefix terms)))

;; Count integer pairs in the disk through the finite square
;; [-BOUND,BOUND]^2.  Calls from the integral use BOUND=2*RADIUS; throughout
;; the integration square this contains every integer pair satisfying the
;; disk inequality, so the count is exactly the source function A(x,y).
(defun putnam-1982-b2-lattice-row-count
    (m-coordinate n-count bound radius-squared)
  (declare (xargs :measure (nfix n-count)))
  (if (zp n-count)
      0
    (let* ((index (- n-count 1))
           (n-coordinate (- index bound)))
      (+ (if (<= (+ (* m-coordinate m-coordinate)
                     (* n-coordinate n-coordinate))
                  radius-squared)
             1
           0)
         (putnam-1982-b2-lattice-row-count
          m-coordinate index bound radius-squared)))))

(defun putnam-1982-b2-lattice-count-rows
    (m-count n-count bound radius-squared)
  (declare (xargs :measure (nfix m-count)))
  (if (zp m-count)
      0
    (let* ((index (- m-count 1))
           (m-coordinate (- index bound)))
      (+ (putnam-1982-b2-lattice-row-count
          m-coordinate n-count bound radius-squared)
         (putnam-1982-b2-lattice-count-rows
          index n-count bound radius-squared)))))

(defun putnam-1982-b2-lattice-count (x y radius)
  (let* ((radius-squared (+ (* x x) (* y y)))
         (bound (* 2 radius))
         (coordinate-count (+ 1 (* 2 bound))))
    (putnam-1982-b2-lattice-count-rows
     coordinate-count coordinate-count bound radius-squared)))

;; Midpoints of the uniform mesh on [-RADIUS,RADIUS].
(defun putnam-1982-b2-grid-coordinate
    (index radius subdivisions)
  (/ (- (+ (* 2 index) 1)
        (* 2 radius subdivisions))
     (* 2 subdivisions)))

(defun putnam-1982-b2-integral-row-sum
    (x-count y radius subdivisions scale)
  (declare (xargs :measure (nfix x-count)))
  (if (zp x-count)
      0
    (let* ((index (- x-count 1))
           (x (putnam-1982-b2-grid-coordinate
               index radius subdivisions))
           (radius-squared (+ (* x x) (* y y))))
      (+ (* (putnam-1982-b2-lattice-count x y radius)
            (putnam-1982-b2-gaussian-approx
             radius-squared scale))
         (putnam-1982-b2-integral-row-sum
          index y radius subdivisions scale)))))

(defun putnam-1982-b2-integral-grid-sum
    (y-count side-count radius subdivisions scale)
  (declare (xargs :measure (nfix y-count)))
  (if (zp y-count)
      0
    (let* ((index (- y-count 1))
           (y (putnam-1982-b2-grid-coordinate
               index radius subdivisions)))
      (+ (putnam-1982-b2-integral-row-sum
          side-count y radius subdivisions scale)
         (putnam-1982-b2-integral-grid-sum
          index side-count radius subdivisions scale)))))

;; This midpoint sum retains the source integrand A(x,y)*exp(-x^2-y^2).
;; Increasing RADIUS removes the Gaussian tail, increasing SUBDIVISIONS
;; resolves the finitely many circle discontinuities in each square, and
;; increasing SCALE removes the rational exponential approximation error.
(defun putnam-1982-b2-integral-approx
    (radius subdivisions scale)
  (if (and (posp radius)
           (posp subdivisions)
           (posp scale))
      (let ((side-count (* 2 radius subdivisions)))
        (/ (putnam-1982-b2-integral-grid-sum
            side-count side-count radius subdivisions scale)
           (* subdivisions subdivisions)))
    0))

;; Exact rational prefixes for g=sum_(k>=0) exp(-k^2).
(defun putnam-1982-b2-g-prefix (terms scale)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-1982-b2-g-prefix index scale)
         (putnam-1982-b2-gaussian-approx
          (* index index) scale)))))

;; The source solution polynomial is pi*(2*X-1)^2.
(defun putnam-1982-b2-solution-approx
    (g-terms pi-terms scale)
  (let ((two-g-minus-one
         (- (* 2 (putnam-1982-b2-g-prefix g-terms scale))
            1)))
    (* (putnam-1982-b2-pi-prefix pi-terms)
       two-g-minus-one
       two-g-minus-one)))

;; No numerical convergence modulus is assumed.  For fixed finite data,
;; SCALE tending to infinity gives the exact exponential values.  Then
;; SUBDIVISIONS tending to infinity gives the integral on a fixed square.
;; Finally RADIUS tends to infinity while G-TERMS and PI-TERMS tend to
;; infinity.  Thus the nested predicates below state equality of the exact
;; iterated limits, not a bounded finite approximation.  The square midpoint
;; integrals converge to the source Lebesgue integral because the integrand
;; is bounded and Riemann integrable on every square; its discontinuities
;; there lie on finitely many circles.  The nonnegative Gaussian tail makes
;; the expanding-square limit the full integral.  Positive rational
;; tolerances are cofinal among positive real tolerances.

(defun-sk putnam-1982-b2-scale-tail-p
    (epsilon radius subdivisions g-terms pi-terms scale-cutoff)
  (forall (scale)
    (implies
     (and
      (posp scale)
      (<= scale-cutoff scale))
     (< (abs
         (- (putnam-1982-b2-integral-approx
             radius subdivisions scale)
            (putnam-1982-b2-solution-approx
             g-terms pi-terms scale)))
        epsilon))))

(defun-sk putnam-1982-b2-scale-cutoff-exists-p
    (epsilon radius subdivisions g-terms pi-terms)
  (exists (scale-cutoff)
    (and
     (posp scale-cutoff)
     (putnam-1982-b2-scale-tail-p
      epsilon radius subdivisions g-terms pi-terms
      scale-cutoff))))

(defun-sk putnam-1982-b2-subdivision-tail-p
    (epsilon radius g-terms pi-terms subdivisions-cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= subdivisions-cutoff subdivisions))
     (putnam-1982-b2-scale-cutoff-exists-p
      epsilon radius subdivisions g-terms pi-terms))))

(defun-sk putnam-1982-b2-subdivision-cutoff-exists-p
    (epsilon radius g-terms pi-terms)
  (exists (subdivisions-cutoff)
    (and
     (posp subdivisions-cutoff)
     (putnam-1982-b2-subdivision-tail-p
      epsilon radius g-terms pi-terms
      subdivisions-cutoff))))

(defun-sk putnam-1982-b2-outer-tail-p
    (epsilon radius-cutoff g-terms-cutoff pi-terms-cutoff)
  (forall (radius g-terms pi-terms)
    (implies
     (and
      (posp radius)
      (<= radius-cutoff radius)
      (posp g-terms)
      (<= g-terms-cutoff g-terms)
      (posp pi-terms)
      (<= pi-terms-cutoff pi-terms))
     (putnam-1982-b2-subdivision-cutoff-exists-p
      epsilon radius g-terms pi-terms))))

(defun-sk putnam-1982-b2-outer-cutoffs-exist-p (epsilon)
  (exists (radius-cutoff g-terms-cutoff pi-terms-cutoff)
    (and
     (posp radius-cutoff)
     (posp g-terms-cutoff)
     (posp pi-terms-cutoff)
     (putnam-1982-b2-outer-tail-p
      epsilon radius-cutoff g-terms-cutoff
      pi-terms-cutoff))))

(defun-sk putnambench-putnam-1982-b2-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1982-b2-outer-cutoffs-exist-p
      epsilon))))

(value-triple :itpeval-statement-checked)
:q
