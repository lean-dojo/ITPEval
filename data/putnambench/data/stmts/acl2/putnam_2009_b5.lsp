;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_b5:
;; a differentiable real function satisfying the stated nonlinear differential
;; equation on (1,infinity) tends to positive infinity. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; JET(0,x,epsilon) and JET(1,x,epsilon) are rational regular-Cauchy
;; approximations to f(x) and f'(x) at rational x>1. DEFSTUB makes JET an
;; arbitrary function symbol, so the statement is a generic schema over
;; unrestricted jet interpretations.
;;
;; Compact continuity gives unique real extensions of both jet levels.
;; The uniform difference-quotient condition on compact subintervals says
;; that level 1 is the derivative of level 0. This C1 presentation is
;; equivalent under the differential equation: differentiability makes f
;; continuous, and the displayed continuous right-hand side makes f'
;; continuous.
;;
;; The equation is cross-multiplied by x^2*(f(x)^2+1), which is strictly
;; positive for x>1. Its error-controlled residual is zero exactly when the
;; source equation holds. The conclusion has the internal scope
;;
;;   forall target, exists cutoff, forall x>cutoff,
;;   exists positive margin, forall precision.
;;
;; Rational points and thresholds are cofinal in the reals, and compact
;; continuity transfers these dense rational formulations to all real inputs.
;; No statement hypothesis contains the requested limit conclusion.

(defstub putnam-2009-b5-jet (order x epsilon) t)

(defun putnam-2009-b5-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun putnam-2009-b5-jet-order-p (order)
  (and
   (natp order)
   (<= order 1)))

(defun putnam-2009-b5-compact-point-p (x bound)
  (and
   (rationalp x)
   (posp bound)
   (< 1 bound)
   (<= (+ 1 (/ 1 bound)) x)
   (<= x bound)))

(defun putnam-2009-b5-minimum (left right)
  (if (< left right) left right))

;; Each jet value is a regular Cauchy name for an exact real.

(defun-sk putnam-2009-b5-regular-jet-p ()
  (forall (order x epsilon eta)
    (implies
     (and
      (putnam-2009-b5-jet-order-p order)
      (rationalp x)
      (< 1 x)
      (putnam-2009-b5-positive-rational-p epsilon)
      (putnam-2009-b5-positive-rational-p eta))
     (let ((left
            (putnam-2009-b5-jet
             order x epsilon))
           (right
            (putnam-2009-b5-jet
             order x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<=
         (abs (- left right))
         (+ epsilon eta)))))))

;; MARGIN bounds the exact distance between two represented jet values.

(defun-sk putnam-2009-b5-value-distance-at-most-p
    (order x y margin)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2009-b5-positive-rational-p epsilon)
      (putnam-2009-b5-positive-rational-p eta))
     (let ((left
            (putnam-2009-b5-jet
             order x epsilon))
           (right
            (putnam-2009-b5-jet
             order y eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<=
         (abs (- left right))
         (+ margin epsilon eta)))))))

(defun-sk putnam-2009-b5-value-distance-below-p
    (order x y epsilon)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin epsilon)
     (putnam-2009-b5-value-distance-at-most-p
      order x y margin))))

(defun-sk putnam-2009-b5-continuity-radius-p
    (order bound epsilon delta)
  (forall (x y)
    (implies
     (and
      (putnam-2009-b5-compact-point-p
       x bound)
      (putnam-2009-b5-compact-point-p
       y bound)
      (< (abs (- x y)) delta))
     (putnam-2009-b5-value-distance-below-p
      order x y epsilon))))

(defun-sk putnam-2009-b5-continuity-radius-exists-p
    (order bound epsilon)
  (exists (delta)
    (and
     (putnam-2009-b5-positive-rational-p delta)
     (putnam-2009-b5-continuity-radius-p
      order bound epsilon delta))))

(defun-sk putnam-2009-b5-compact-continuity-p ()
  (forall (order bound epsilon)
    (implies
     (and
      (putnam-2009-b5-jet-order-p order)
      (posp bound)
      (< 1 bound)
      (putnam-2009-b5-positive-rational-p epsilon))
     (putnam-2009-b5-continuity-radius-exists-p
      order bound epsilon))))

;; MARGIN bounds the exact error between the difference quotient of level 0
;; and the represented level-1 derivative. The three approximation errors are
;; displayed explicitly.

(defun-sk putnam-2009-b5-derivative-error-at-most-p
    (x h margin)
  (forall
      (left-precision right-precision derivative-precision)
    (implies
     (and
      (putnam-2009-b5-positive-rational-p
       left-precision)
      (putnam-2009-b5-positive-rational-p
       right-precision)
      (putnam-2009-b5-positive-rational-p
       derivative-precision))
     (let* ((left
             (putnam-2009-b5-jet
              0 x left-precision))
            (right
             (putnam-2009-b5-jet
              0 (+ x h) right-precision))
            (derivative
             (putnam-2009-b5-jet
              1 x derivative-precision))
            (quotient
             (/ (- right left) h))
            (error-allowance
             (+
              margin
              (/ left-precision (abs h))
              (/ right-precision (abs h))
              derivative-precision)))
       (and
        (rationalp left)
        (rationalp right)
        (rationalp derivative)
        (<=
         (abs (- quotient derivative))
         error-allowance))))))

(defun-sk putnam-2009-b5-derivative-error-below-p
    (x h epsilon)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin epsilon)
     (putnam-2009-b5-derivative-error-at-most-p
      x h margin))))

(defun-sk putnam-2009-b5-derivative-radius-p
    (bound epsilon delta)
  (forall (x h)
    (implies
     (and
      (putnam-2009-b5-compact-point-p
       x bound)
      (rationalp h)
      (not (equal h 0))
      (putnam-2009-b5-compact-point-p
       (+ x h) bound)
      (< (abs h) delta))
     (putnam-2009-b5-derivative-error-below-p
      x h epsilon))))

(defun-sk putnam-2009-b5-derivative-radius-exists-p
    (bound epsilon)
  (exists (delta)
    (and
     (putnam-2009-b5-positive-rational-p delta)
     (putnam-2009-b5-derivative-radius-p
      bound epsilon delta))))

(defun-sk putnam-2009-b5-derivative-on-compacts-p ()
  (forall (bound epsilon)
    (implies
     (and
      (posp bound)
      (< 1 bound)
      (putnam-2009-b5-positive-rational-p epsilon))
     (putnam-2009-b5-derivative-radius-exists-p
      bound epsilon))))

(defun putnam-2009-b5-c1-jet-p ()
  (and
   (putnam-2009-b5-regular-jet-p)
   (putnam-2009-b5-compact-continuity-p)
   (putnam-2009-b5-derivative-on-compacts-p)))

;; Adaptive precision makes the cross-multiplied ODE residual converge to its
;; exact real value while keeping every ACL2 arithmetic operation rational.

(defun putnam-2009-b5-equation-precision
    (x epsilon)
  (let* ((x-square (* x x))
         (value-at-one
          (putnam-2009-b5-jet 0 x 1))
         (derivative-at-one
          (putnam-2009-b5-jet 1 x 1))
         (value-bound
          (+ 2 (abs value-at-one)))
         (derivative-bound
          (+ 2 (abs derivative-at-one)))
         (scale
          (*
           8
           (+ 1 x-square)
           (+ 1 derivative-bound)
           (+ 1 value-bound)
           (+ 1 value-bound))))
    (putnam-2009-b5-minimum
     1
     (/ epsilon scale))))

(defun-sk putnam-2009-b5-equation-p ()
  (forall (x epsilon)
    (implies
     (and
      (rationalp x)
      (< 1 x)
      (putnam-2009-b5-positive-rational-p epsilon))
     (let* ((x-square (* x x))
            (value-at-one
             (putnam-2009-b5-jet 0 x 1))
            (derivative-at-one
             (putnam-2009-b5-jet 1 x 1))
            (precision
             (putnam-2009-b5-equation-precision
              x epsilon))
            (value
             (putnam-2009-b5-jet
              0 x precision))
            (derivative
             (putnam-2009-b5-jet
              1 x precision))
            (value-square (* value value))
            (left
             (* derivative
                x-square
                (+ value-square 1)))
            (right
             (- x-square value-square)))
       (and
        (rationalp value-at-one)
        (rationalp derivative-at-one)
        (putnam-2009-b5-positive-rational-p
         precision)
        (rationalp value)
        (rationalp derivative)
        (<= (abs (- left right))
            epsilon))))))

;; A positive MARGIN valid at every precision is exactly the strict real
;; inequality f(x)>TARGET.

(defun-sk putnam-2009-b5-limit-margin-p
    (target x margin)
  (forall (epsilon)
    (implies
     (putnam-2009-b5-positive-rational-p epsilon)
     (let ((value
            (putnam-2009-b5-jet
             0 x epsilon)))
       (and
        (rationalp value)
        (<=
         margin
         (+ (- value target) epsilon)))))))

(defun-sk putnam-2009-b5-limit-margin-exists-p
    (target x)
  (exists (margin)
    (and
     (putnam-2009-b5-positive-rational-p margin)
     (putnam-2009-b5-limit-margin-p
      target x margin))))

(defun-sk putnam-2009-b5-limit-tail-p
    (target cutoff)
  (forall (x)
    (implies
     (and
      (rationalp x)
      (< cutoff x))
     (putnam-2009-b5-limit-margin-exists-p
      target x))))

(defun-sk putnam-2009-b5-limit-cutoff-exists-p
    (target)
  (exists (cutoff)
    (and
     (rationalp cutoff)
     (< 1 cutoff)
     (putnam-2009-b5-limit-tail-p
      target cutoff))))

(defun-sk putnam-2009-b5-limit-p ()
  (forall (target)
    (implies
     (rationalp target)
     (putnam-2009-b5-limit-cutoff-exists-p
      target))))

(defun putnambench-putnam-2009-b5-statement ()
  (implies
   (and
    (putnam-2009-b5-c1-jet-p)
    (putnam-2009-b5-equation-p))
   (putnam-2009-b5-limit-p)))

(value-triple :itpeval-statement-checked)
:q
