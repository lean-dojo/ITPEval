;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_b5:
;; every continuous real function satisfying g(g(x)) = a*g(x) + b*x for real
;; 0 < a,b < 1/2 is linear through the origin. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative symbols provide arbitrary rational regular Cauchy names
;; for a, b, and the value g(x) at each rational x. They are not APPLY$ codes
;; or finite tables. Regular names cover every real number, and compact
;; uniform continuity on the rational line is equivalent to a unique
;; continuous extension g : R -> R.
;;
;; The functional equation is equality of the limits of its rational
;; approximations. It is imposed at every rational x and hence, by continuity,
;; at every real x. The conclusion uses the forced slope g(1): a function of
;; the form g(x)=c*x has c=g(1), so this is equivalent in both directions to
;; the source conclusion that some real c works for every real x.

(defstub putnam-2001-b5-a-approx (epsilon) t)
(defstub putnam-2001-b5-b-approx (epsilon) t)
(defstub putnam-2001-b5-g-approx (x epsilon) t)

(defun putnam-2001-b5-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun putnam-2001-b5-rational-in-bound-p (x bound)
  (and
   (rationalp x)
   (<= (- bound) x)
   (<= x bound)))

(defun putnam-2001-b5-coefficient-approx (which epsilon)
  (if (equal which :a)
      (putnam-2001-b5-a-approx epsilon)
    (putnam-2001-b5-b-approx epsilon)))

(defun-sk putnam-2001-b5-coefficient-real-name-p (which)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2001-b5-positive-rational-p epsilon)
      (putnam-2001-b5-positive-rational-p eta))
     (let ((left
            (putnam-2001-b5-coefficient-approx
             which epsilon))
           (right
            (putnam-2001-b5-coefficient-approx
             which eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun-sk putnam-2001-b5-coefficient-lower-bound-p
    (which lower)
  (forall (epsilon)
    (implies
     (putnam-2001-b5-positive-rational-p epsilon)
     (<=
      lower
      (+ (putnam-2001-b5-coefficient-approx
          which epsilon)
         epsilon)))))

(defun-sk putnam-2001-b5-coefficient-half-gap-p
    (which gap)
  (forall (epsilon)
    (implies
     (putnam-2001-b5-positive-rational-p epsilon)
     (<=
      gap
      (+ (- 1/2
            (putnam-2001-b5-coefficient-approx
             which epsilon))
         epsilon)))))

(defun-sk putnam-2001-b5-coefficient-in-open-half-p (which)
  (exists (lower gap)
    (and
     (putnam-2001-b5-positive-rational-p lower)
     (putnam-2001-b5-positive-rational-p gap)
     (putnam-2001-b5-coefficient-lower-bound-p
      which lower)
     (putnam-2001-b5-coefficient-half-gap-p
      which gap))))

(defun-sk putnam-2001-b5-function-real-name-p ()
  (forall (x epsilon eta)
    (implies
     (and
      (rationalp x)
      (putnam-2001-b5-positive-rational-p epsilon)
      (putnam-2001-b5-positive-rational-p eta))
     (let ((left
            (putnam-2001-b5-g-approx x epsilon))
           (right
            (putnam-2001-b5-g-approx x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; Exact distance at most MARGIN between the represented values g(x), g(y).

(defun-sk putnam-2001-b5-value-distance-at-most-p
    (x y margin)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2001-b5-positive-rational-p epsilon)
      (putnam-2001-b5-positive-rational-p eta))
     (<=
      (abs
       (-
        (putnam-2001-b5-g-approx x epsilon)
        (putnam-2001-b5-g-approx y eta)))
      (+ margin epsilon eta)))))

;; Rational density makes this equivalent to exact distance below EPSILON.

(defun-sk putnam-2001-b5-value-distance-below-p
    (x y epsilon)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin epsilon)
     (putnam-2001-b5-value-distance-at-most-p
      x y margin))))

(defun-sk putnam-2001-b5-uniform-radius-p
    (bound epsilon delta)
  (forall (x y)
    (implies
     (and
      (putnam-2001-b5-rational-in-bound-p x bound)
      (putnam-2001-b5-rational-in-bound-p y bound)
      (< (abs (- x y)) delta))
     (putnam-2001-b5-value-distance-below-p
      x y epsilon))))

(defun-sk putnam-2001-b5-uniform-radius-exists-p
    (bound epsilon)
  (exists (delta)
    (and
     (putnam-2001-b5-positive-rational-p delta)
     (putnam-2001-b5-uniform-radius-p
      bound epsilon delta))))

(defun-sk putnam-2001-b5-continuous-extension-p ()
  (forall (bound epsilon)
    (implies
     (and
      (posp bound)
      (putnam-2001-b5-positive-rational-p epsilon))
     (putnam-2001-b5-uniform-radius-exists-p
      bound epsilon))))

;; For fixed rational x, these expressions converge respectively to
;; g(g(x)) and a*g(x)+b*x. Requiring arbitrarily fine residuals is therefore
;; exact equality of the represented real limits.

(defun-sk putnam-2001-b5-equation-precision-exists-p
    (x epsilon)
  (exists (precision)
    (and
     (putnam-2001-b5-positive-rational-p precision)
     (< precision epsilon)
     (<
      (abs
       (-
        (putnam-2001-b5-g-approx
         (putnam-2001-b5-g-approx x precision)
         precision)
        (+
         (*
          (putnam-2001-b5-a-approx precision)
          (putnam-2001-b5-g-approx x precision))
         (*
          (putnam-2001-b5-b-approx precision)
          x))))
      epsilon))))

(defun-sk putnam-2001-b5-functional-equation-p ()
  (forall (x epsilon)
    (implies
     (and
      (rationalp x)
      (putnam-2001-b5-positive-rational-p epsilon))
     (putnam-2001-b5-equation-precision-exists-p
      x epsilon))))

;; The exact represented equality g(x)=g(1)*x on all rational x extends by
;; continuity to all real x.

(defun-sk putnam-2001-b5-linear-precision-exists-p
    (x epsilon)
  (exists (precision)
    (and
     (putnam-2001-b5-positive-rational-p precision)
     (< precision epsilon)
     (<
      (abs
       (-
        (putnam-2001-b5-g-approx x precision)
        (*
         (putnam-2001-b5-g-approx 1 precision)
         x)))
      epsilon))))

(defun-sk putnam-2001-b5-linear-through-origin-p ()
  (forall (x epsilon)
    (implies
     (and
      (rationalp x)
      (putnam-2001-b5-positive-rational-p epsilon))
     (putnam-2001-b5-linear-precision-exists-p
      x epsilon))))

(defun putnambench-putnam-2001-b5-statement ()
  (implies
   (and
    (putnam-2001-b5-coefficient-real-name-p :a)
    (putnam-2001-b5-coefficient-real-name-p :b)
    (putnam-2001-b5-coefficient-in-open-half-p :a)
    (putnam-2001-b5-coefficient-in-open-half-p :b)
    (putnam-2001-b5-function-real-name-p)
    (putnam-2001-b5-continuous-extension-p)
    (putnam-2001-b5-functional-equation-p))
   (putnam-2001-b5-linear-through-origin-p)))

(value-triple :itpeval-statement-checked)
:q
