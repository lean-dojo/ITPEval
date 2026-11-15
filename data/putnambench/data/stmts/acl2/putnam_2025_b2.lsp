;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_b2:
;; a continuous, strictly increasing, nonnegative real function on [0,1] has
;; smaller planar-region centroid abscissa than its solid-of-revolution
;; centroid abscissa. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; F-APPROX is a generic rational approximation oracle on the rational points
;; of [0,1]. The predicates below make each precision-indexed value a regular
;; Cauchy name and impose uniform continuity. Thus the oracle presents an
;; arbitrary continuous real-valued function on [0,1], rather than restricting
;; the source function or its values to rationals.

(defstub putnam-2025-b2-f-approx (x precision) t)

(defun putnam-2025-b2-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun putnam-2025-b2-unit-rational-p (value)
  (and
   (rationalp value)
   (<= 0 value)
   (<= value 1)))

(defun-sk putnam-2025-b2-regular-value-p (x)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2025-b2-positive-rational-p epsilon)
      (putnam-2025-b2-positive-rational-p eta))
     (let ((left
            (putnam-2025-b2-f-approx x epsilon))
           (right
            (putnam-2025-b2-f-approx x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun-sk putnam-2025-b2-regular-function-p ()
  (forall (x)
    (implies
     (putnam-2025-b2-unit-rational-p x)
     (putnam-2025-b2-regular-value-p x))))

;; For regular names, this is exactly |f(x)-f(y)| <= BOUND.

(defun-sk putnam-2025-b2-value-distance-at-most-p
    (x y bound)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2025-b2-positive-rational-p epsilon)
      (putnam-2025-b2-positive-rational-p eta))
     (<=
      (abs
       (-
        (putnam-2025-b2-f-approx x epsilon)
        (putnam-2025-b2-f-approx y eta)))
      (+ bound epsilon eta)))))

;; A rational upper bound strictly below RADIUS makes this exactly the strict
;; inequality |f(x)-f(y)| < RADIUS.

(defun-sk putnam-2025-b2-value-distance-below-p
    (x y radius)
  (exists (bound)
    (and
     (rationalp bound)
     (<= 0 bound)
     (< bound radius)
     (putnam-2025-b2-value-distance-at-most-p
      x y bound))))

(defun-sk putnam-2025-b2-continuity-delta-p
    (epsilon delta)
  (forall (x y)
    (implies
     (and
      (putnam-2025-b2-unit-rational-p x)
      (putnam-2025-b2-unit-rational-p y)
      (< (abs (- x y)) delta))
     (putnam-2025-b2-value-distance-below-p
      x y epsilon))))

(defun-sk putnam-2025-b2-continuity-delta-exists-p
    (epsilon)
  (exists (delta)
    (and
     (putnam-2025-b2-positive-rational-p delta)
     (putnam-2025-b2-continuity-delta-p
      epsilon delta))))

;; Continuity on the compact interval is equivalent to this uniform
;; continuity condition on its dense rational subset.

(defun-sk putnam-2025-b2-continuous-on-unit-p ()
  (forall (epsilon)
    (implies
     (putnam-2025-b2-positive-rational-p epsilon)
     (putnam-2025-b2-continuity-delta-exists-p
      epsilon))))

;; For regular names, VALUE-GAP-AT-LEAST-P states
;; f(x) + GAP <= f(y). Existence of a positive rational gap is therefore
;; exactly f(x) < f(y).

(defun-sk putnam-2025-b2-value-gap-at-least-p
    (x y gap)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2025-b2-positive-rational-p epsilon)
      (putnam-2025-b2-positive-rational-p eta))
     (<=
      (+ (putnam-2025-b2-f-approx x epsilon)
         gap)
      (+ (putnam-2025-b2-f-approx y eta)
         epsilon
         eta)))))

(defun-sk putnam-2025-b2-value-strictly-below-p
    (x y)
  (exists (gap)
    (and
     (putnam-2025-b2-positive-rational-p gap)
     (putnam-2025-b2-value-gap-at-least-p
      x y gap))))

(defun-sk putnam-2025-b2-strictly-increasing-p ()
  (forall (x y)
    (implies
     (and
      (putnam-2025-b2-unit-rational-p x)
      (putnam-2025-b2-unit-rational-p y)
      (< x y))
     (putnam-2025-b2-value-strictly-below-p
      x y))))

;; A regular Cauchy name has nonnegative limit exactly when every
;; precision-EPSILON approximation is at least -EPSILON.

(defun-sk putnam-2025-b2-value-nonnegative-p (x)
  (forall (epsilon)
    (implies
     (putnam-2025-b2-positive-rational-p epsilon)
     (<= (- epsilon)
         (putnam-2025-b2-f-approx x epsilon)))))

(defun-sk putnam-2025-b2-nonnegative-on-unit-p ()
  (forall (x)
    (implies
     (putnam-2025-b2-unit-rational-p x)
     (putnam-2025-b2-value-nonnegative-p x))))

;; Uniform midpoint Riemann sums converge to the interval integrals of f,
;; x*f, f^2, and x*f^2. The approximation precision is the reciprocal of the
;; grid size, so both sampling and value errors tend to zero without bounding
;; the grid or the represented real values.

(defun putnam-2025-b2-integrand-approx
    (mode x precision)
  (let ((value
         (putnam-2025-b2-f-approx x precision)))
    (cond
     ((equal mode 'f)
      value)
     ((equal mode 'x-times-f)
      (* x value))
     ((equal mode 'f-squared)
      (* value value))
     ((equal mode 'x-times-f-squared)
      (* x value value))
     (t 0))))

(defun putnam-2025-b2-riemann-sum
    (mode count grid-size precision)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((midpoint
           (/ (- (* 2 count) 1)
              (* 2 grid-size))))
      (+
       (putnam-2025-b2-integrand-approx
        mode midpoint precision)
       (putnam-2025-b2-riemann-sum
        mode (- count 1) grid-size precision)))))

(defun putnam-2025-b2-integral-prefix
    (mode grid-size)
  (if (posp grid-size)
      (let ((precision (/ 1 grid-size)))
        (/
         (putnam-2025-b2-riemann-sum
          mode grid-size grid-size precision)
         grid-size))
    0))

(defun putnam-2025-b2-left-product-prefix
    (grid-size)
  (*
   (putnam-2025-b2-integral-prefix
    'x-times-f grid-size)
   (putnam-2025-b2-integral-prefix
    'f-squared grid-size)))

(defun putnam-2025-b2-right-product-prefix
    (grid-size)
  (*
   (putnam-2025-b2-integral-prefix
    'x-times-f-squared grid-size)
   (putnam-2025-b2-integral-prefix
    'f grid-size)))

;; Strict inequality of the two real product limits is equivalent to the
;; existence of an eventual positive rational gap between their prefixes.

(defun-sk putnam-2025-b2-product-gap-eventually-p
    (gap cutoff)
  (forall (grid-size)
    (implies
     (and
      (posp grid-size)
      (natp cutoff)
      (<= cutoff grid-size))
     (<=
      (+
       (putnam-2025-b2-left-product-prefix
        grid-size)
       gap)
      (putnam-2025-b2-right-product-prefix
       grid-size)))))

(defun-sk putnam-2025-b2-centroid-inequality-p ()
  (exists (gap cutoff)
    (and
     (putnam-2025-b2-positive-rational-p gap)
     (natp cutoff)
     (putnam-2025-b2-product-gap-eventually-p
      gap cutoff))))

;; Strict increase and nonnegativity make both centroid denominators positive.
;; Cross multiplication therefore turns the source quotient inequality into
;; exactly the product-limit inequality above.

(defun putnambench-putnam-2025-b2-statement ()
  (implies
   (and
    (putnam-2025-b2-regular-function-p)
    (putnam-2025-b2-continuous-on-unit-p)
    (putnam-2025-b2-strictly-increasing-p)
    (putnam-2025-b2-nonnegative-on-unit-p))
   (putnam-2025-b2-centroid-inequality-p)))

(value-triple :itpeval-statement-checked)
:q
