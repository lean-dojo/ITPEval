;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_b6:
;; the sharp real threshold for the normalized exponential power series is
;; c = -1/2, with decay below c and divergence above c. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source hypothesis determines F uniquely on 0 <= x < 1, so F is
;; eliminated definitionally.  After multiplication by exp(-1/(1-x)), its
;; n-th positive term is
;;
;;   exp(a*log(n) + 2*n + n^2*log(x) - 1/(1-x)).
;;
;; For positive rational x, the functions below give shrinking rational
;; intervals for log(x) and exp(x), hence for every finite partial sum.
;; Positivity makes "all finite partial sums are below epsilon" equivalent,
;; after the usual epsilon rescaling, to the normalized series tending to
;; zero.  Likewise, a finite partial sum above every rational target is
;; equivalent to divergence to positive infinity.
;;
;; The DEFSTUB below is an arbitrary rational approximation function for the
;; threshold c. Its regular-Cauchy law is explicit in the root predicate, so
;; no computability or first-class-function restriction is imposed. Rational
;; a values suffice without narrowing the theorem: they are dense, and the
;; positive summands are monotone in a. Rational x values suffice because the
;; normalized series is continuous at every x in (0,1). DEFUN-SK keeps every
;; universal quantifier and every limit witness inside the statement.

;; Exact real names and comparisons with rationals.

(defstub putnam-2024-b6-c-approx (precision) t)

(defun-sk putnam-2024-b6-real-cauchy-p ()
  (forall (epsilon eta)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon)
          (rationalp eta)
          (< 0 eta))
     (let ((left
            (putnam-2024-b6-c-approx epsilon))
           (right
            (putnam-2024-b6-c-approx eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun-sk putnam-2024-b6-rational-lower-bound-p (lower)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (let ((value
            (putnam-2024-b6-c-approx epsilon)))
       (and
        (rationalp value)
        (<= lower (+ value epsilon)))))))

(defun-sk putnam-2024-b6-rational-less-real-p
    (rational-value)
  (exists (margin)
    (and
     (rationalp rational-value)
     (rationalp margin)
     (< 0 margin)
     (putnam-2024-b6-rational-lower-bound-p
      (+ rational-value margin)))))

(defun-sk putnam-2024-b6-rational-upper-bound-p (upper)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (let ((value
            (putnam-2024-b6-c-approx epsilon)))
       (and
        (rationalp value)
        (<= (- value epsilon) upper))))))

(defun-sk putnam-2024-b6-real-less-rational-p
    (rational-value)
  (exists (margin)
    (and
     (rationalp rational-value)
     (rationalp margin)
     (< 0 margin)
     (putnam-2024-b6-rational-upper-bound-p
      (- rational-value margin)))))

(defun-sk putnam-2024-b6-real-equal-rational-p
    (rational-value)
  (forall (epsilon)
    (implies
     (and (rationalp rational-value)
          (rationalp epsilon)
          (< 0 epsilon))
     (let ((value
            (putnam-2024-b6-c-approx epsilon)))
       (and
        (rationalp value)
        (<= (abs (- value rational-value))
            epsilon))))))

;; Rational interval enclosures for log and exp.

(defun putnam-2024-b6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2024-b6-factorial (- n 1)))))

(defun putnam-2024-b6-exp-series (x degree)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      1
    (+ (putnam-2024-b6-exp-series
        x (- degree 1))
       (/ (expt x degree)
          (putnam-2024-b6-factorial degree)))))

(defun putnam-2024-b6-nonnegative-part (x)
  (if (< x 0) 0 x))

(defun putnam-2024-b6-exp-scale (x)
  (+ 1 (floor (abs x) 1)))

(defun putnam-2024-b6-exp-reduced-argument (x)
  (/ x (putnam-2024-b6-exp-scale x)))

(defun putnam-2024-b6-exp-tail (x degree)
  (let* ((y
          (putnam-2024-b6-exp-reduced-argument x))
         (next (+ 1 (nfix degree))))
    (/ (expt (abs y) next)
       (* (putnam-2024-b6-factorial next)
          (- 1 (abs y))))))

(defun putnam-2024-b6-exp-lower (x degree)
  (let* ((scale
          (putnam-2024-b6-exp-scale x))
         (reduced
          (putnam-2024-b6-exp-reduced-argument x))
         (center
          (putnam-2024-b6-exp-series reduced degree))
         (radius
          (putnam-2024-b6-exp-tail x degree)))
    (expt
     (putnam-2024-b6-nonnegative-part
      (- center radius))
     scale)))

(defun putnam-2024-b6-exp-upper (x degree)
  (let* ((scale
          (putnam-2024-b6-exp-scale x))
         (reduced
          (putnam-2024-b6-exp-reduced-argument x))
         (center
          (putnam-2024-b6-exp-series reduced degree))
         (radius
          (putnam-2024-b6-exp-tail x degree)))
    (expt (+ center radius) scale)))

(defun putnam-2024-b6-log-series (z degree)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (* 2 z)
    (+ (putnam-2024-b6-log-series
        z (- degree 1))
       (/ (* 2
             (expt z (+ (* 2 degree) 1)))
          (+ (* 2 degree) 1)))))

(defun putnam-2024-b6-log-tail (z degree)
  (let ((next-odd (+ (* 2 (nfix degree)) 3)))
    (/ (* 2 (expt (abs z) next-odd))
       (* next-odd
          (- 1 (* z z))))))

(defun putnam-2024-b6-log-lower (x degree)
  (let* ((z (/ (- x 1) (+ x 1)))
         (center
          (putnam-2024-b6-log-series z degree))
         (radius
          (putnam-2024-b6-log-tail z degree)))
    (- center radius)))

(defun putnam-2024-b6-log-upper (x degree)
  (let* ((z (/ (- x 1) (+ x 1)))
         (center
          (putnam-2024-b6-log-series z degree))
         (radius
          (putnam-2024-b6-log-tail z degree)))
    (+ center radius)))

(defun putnam-2024-b6-scale-interval-lower
    (scalar lower upper)
  (if (< scalar 0)
      (* scalar upper)
    (* scalar lower)))

(defun putnam-2024-b6-scale-interval-upper
    (scalar lower upper)
  (if (< scalar 0)
      (* scalar lower)
    (* scalar upper)))

(defun putnam-2024-b6-exponent-lower
    (a x n degree)
  (let* ((log-n-lower
          (putnam-2024-b6-log-lower n degree))
         (log-n-upper
          (putnam-2024-b6-log-upper n degree))
         (log-x-lower
          (putnam-2024-b6-log-lower x degree)))
    (+ (putnam-2024-b6-scale-interval-lower
        a log-n-lower log-n-upper)
       (* n n log-x-lower)
       (* 2 n)
       (- (/ 1 (- 1 x))))))

(defun putnam-2024-b6-exponent-upper
    (a x n degree)
  (let* ((log-n-lower
          (putnam-2024-b6-log-lower n degree))
         (log-n-upper
          (putnam-2024-b6-log-upper n degree))
         (log-x-upper
          (putnam-2024-b6-log-upper x degree)))
    (+ (putnam-2024-b6-scale-interval-upper
        a log-n-lower log-n-upper)
       (* n n log-x-upper)
       (* 2 n)
       (- (/ 1 (- 1 x))))))

(defun putnam-2024-b6-term-lower
    (a x n degree)
  (putnam-2024-b6-exp-lower
   (putnam-2024-b6-exponent-lower
    a x n degree)
   degree))

(defun putnam-2024-b6-term-upper
    (a x n degree)
  (putnam-2024-b6-exp-upper
   (putnam-2024-b6-exponent-upper
    a x n degree)
   degree))

(defun putnam-2024-b6-partial-sum-lower
    (a x terms degree)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (putnam-2024-b6-partial-sum-lower
        a x (- terms 1) degree)
       (putnam-2024-b6-term-lower
        a x terms degree))))

(defun putnam-2024-b6-partial-sum-upper
    (a x terms degree)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (putnam-2024-b6-partial-sum-upper
        a x (- terms 1) degree)
       (putnam-2024-b6-term-upper
        a x terms degree))))

;; The zero-limit half of the threshold property.

(defun-sk putnam-2024-b6-upper-certificate-exists-p
    (a x terms epsilon)
  (exists (degree)
    (and
     (natp degree)
     (< (putnam-2024-b6-partial-sum-upper
         a x terms degree)
        epsilon))))

(defun-sk putnam-2024-b6-zero-tail-p
    (delta a epsilon)
  (forall (x terms)
    (implies
     (and
      (rationalp x)
      (< 0 x)
      (< x 1)
      (< (- 1 x) delta)
      (natp terms))
     (putnam-2024-b6-upper-certificate-exists-p
      a x terms epsilon))))

(defun putnam-2024-b6-zero-delta-p
    (delta a epsilon)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-2024-b6-zero-tail-p
    delta a epsilon)))

(defun-sk putnam-2024-b6-zero-delta-exists-p
    (a epsilon)
  (exists (delta)
    (putnam-2024-b6-zero-delta-p
     delta a epsilon)))

(defun-sk putnam-2024-b6-zero-limit-p (a)
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2024-b6-zero-delta-exists-p
      a epsilon))))

(defun-sk putnam-2024-b6-zero-side-p ()
  (forall (a)
    (implies
     (and
      (rationalp a)
      (putnam-2024-b6-rational-less-real-p
       a))
     (putnam-2024-b6-zero-limit-p a))))

;; The divergence-to-positive-infinity half.

(defun-sk putnam-2024-b6-lower-witness-exists-p
    (a x target)
  (exists (terms degree)
    (and
     (natp terms)
     (natp degree)
     (< target
        (putnam-2024-b6-partial-sum-lower
         a x terms degree)))))

(defun-sk putnam-2024-b6-infinity-tail-p
    (delta a target)
  (forall (x)
    (implies
     (and
      (rationalp x)
      (< 0 x)
      (< x 1)
      (< (- 1 x) delta))
     (putnam-2024-b6-lower-witness-exists-p
      a x target))))

(defun putnam-2024-b6-infinity-delta-p
    (delta a target)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-2024-b6-infinity-tail-p
    delta a target)))

(defun-sk putnam-2024-b6-infinity-delta-exists-p
    (a target)
  (exists (delta)
    (putnam-2024-b6-infinity-delta-p
     delta a target)))

(defun-sk putnam-2024-b6-infinity-limit-p (a)
  (forall (target)
    (implies
     (rationalp target)
     (putnam-2024-b6-infinity-delta-exists-p
      a target))))

(defun-sk putnam-2024-b6-infinity-side-p ()
  (forall (a)
    (implies
     (and
      (rationalp a)
      (putnam-2024-b6-real-less-rational-p
       a))
     (putnam-2024-b6-infinity-limit-p a))))

(defun putnam-2024-b6-threshold-property-p ()
  (and
   (putnam-2024-b6-zero-side-p)
   (putnam-2024-b6-infinity-side-p)))

(defun putnambench-putnam-2024-b6-statement ()
  (implies
   (putnam-2024-b6-real-cauchy-p)
   (equal
    (if (putnam-2024-b6-threshold-property-p)
        t nil)
    (if (putnam-2024-b6-real-equal-rational-p
         -1/2)
        t nil))))

(value-triple :itpeval-statement-checked)
:q
