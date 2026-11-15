;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_b4:
;; every continuous real function satisfying f(2*x^2-1) = 2*x*f(x) on the
;; real line vanishes on the closed interval [-1,1]. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; F-APPROX(x,epsilon) is a rational approximation to f(x), for rational x
;; and positive rational epsilon. DEFSTUB makes this an arbitrary function
;; symbol, rather than an APPLY$ code or a finite table.
;;
;; The regular Cauchy condition determines one exact real value at every
;; rational x. Uniform continuity on each bounded rational interval is
;; equivalent to a unique continuous extension to the full real line, and
;; every continuous real function supplies such rational approximation data.
;; The functional equation is imposed on the dense rational inputs using
;; exact Cauchy-name equality; continuity extends it to every real input.
;; Likewise, exact zero values on the rational points of [-1,1] are equivalent
;; to vanishing on the full real interval.

(defstub putnam-2000-b4-f-approx (x epsilon) t)

(defun putnam-2000-b4-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun putnam-2000-b4-rational-in-bound-p (x bound)
  (and
   (rationalp x)
   (<= (- bound) x)
   (<= x bound)))

(defun-sk putnam-2000-b4-regular-cauchy-data-p ()
  (forall (x epsilon eta)
    (implies
     (and
      (rationalp x)
      (putnam-2000-b4-positive-rational-p epsilon)
      (putnam-2000-b4-positive-rational-p eta))
     (let ((left
            (putnam-2000-b4-f-approx x epsilon))
           (right
            (putnam-2000-b4-f-approx x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; This predicate states that the exact represented values at x and y differ
;; by at most MARGIN. Approximation errors are included explicitly.

(defun-sk putnam-2000-b4-value-distance-at-most-p
    (x y margin)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2000-b4-positive-rational-p epsilon)
      (putnam-2000-b4-positive-rational-p eta))
     (<=
      (abs
       (-
        (putnam-2000-b4-f-approx x epsilon)
        (putnam-2000-b4-f-approx y eta)))
      (+ margin epsilon eta)))))

;; For exact represented reals, distance < EPSILON iff there is a rational
;; MARGIN < EPSILON that is an upper bound for their distance.

(defun-sk putnam-2000-b4-value-distance-below-p
    (x y epsilon)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin epsilon)
     (putnam-2000-b4-value-distance-at-most-p
      x y margin))))

(defun-sk putnam-2000-b4-uniform-radius-p
    (bound epsilon delta)
  (forall (x y)
    (implies
     (and
      (putnam-2000-b4-rational-in-bound-p x bound)
      (putnam-2000-b4-rational-in-bound-p y bound)
      (< (abs (- x y)) delta))
     (putnam-2000-b4-value-distance-below-p
      x y epsilon))))

(defun-sk putnam-2000-b4-uniform-radius-exists-p
    (bound epsilon)
  (exists (delta)
    (and
     (putnam-2000-b4-positive-rational-p delta)
     (putnam-2000-b4-uniform-radius-p
      bound epsilon delta))))

(defun-sk putnam-2000-b4-continuous-extension-p ()
  (forall (bound epsilon)
    (implies
     (and
      (posp bound)
      (putnam-2000-b4-positive-rational-p epsilon))
     (putnam-2000-b4-uniform-radius-exists-p
      bound epsilon))))

;; Equality of the two represented real values in the functional equation.
;; The right approximation error is scaled by |2*x|.

(defun-sk putnam-2000-b4-functional-equation-p ()
  (forall (x epsilon eta)
    (implies
     (and
      (rationalp x)
      (putnam-2000-b4-positive-rational-p epsilon)
      (putnam-2000-b4-positive-rational-p eta))
     (let* ((factor (* 2 x))
            (transformed (- (* 2 x x) 1))
            (left
             (putnam-2000-b4-f-approx
              transformed epsilon))
            (right
             (* factor
                (putnam-2000-b4-f-approx x eta))))
       (<=
        (abs (- left right))
        (+ epsilon (* (abs factor) eta)))))))

(defun-sk putnam-2000-b4-zero-on-unit-interval-p ()
  (forall (x epsilon)
    (implies
     (and
      (rationalp x)
      (<= -1 x)
      (<= x 1)
      (putnam-2000-b4-positive-rational-p epsilon))
     (<=
      (abs (putnam-2000-b4-f-approx x epsilon))
      epsilon))))

(defun putnambench-putnam-2000-b4-statement ()
  (implies
   (and
    (putnam-2000-b4-regular-cauchy-data-p)
    (putnam-2000-b4-continuous-extension-p)
    (putnam-2000-b4-functional-equation-p))
   (putnam-2000-b4-zero-on-unit-interval-p)))

(value-triple :itpeval-statement-checked)
:q
