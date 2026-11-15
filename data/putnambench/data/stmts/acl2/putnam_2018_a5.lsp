;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_a5:
;; every infinitely differentiable nonnegative real function with f(0)=0 and
;; f(1)=1 has a negative derivative value at some positive order and real
;; point. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; JET(order,x,epsilon) is a rational regular Cauchy name for the value at the
;; rational point x of the order-th derivative. DEFSTUB makes this one
;; function symbol generic without restricting it to an APPLY$-tame class.
;; DEFUN-SK supplies every universal and existential quantifier below.
;;
;; Compact uniform continuity gives each jet level a unique extension to all
;; real x. The uniform difference-quotient condition says that level order+1
;; is the derivative of level order. Hence the accepted jets are exactly
;; smooth real functions together with all iterated derivatives. Exact point
;; values and nonnegativity on the dense rational points extend to all reals.
;; Conversely, continuity makes a negative derivative at a real point
;; equivalent to a negative value with margin at some rational point.
;;
;; The antecedent is non-vacuous: the exact, epsilon-independent jet for x^2
;; has levels x^2, 2*x, 2, 0, 0, ... and satisfies every assumption (with a
;; negative first derivative at x=-1).

(defstub putnam-2018-a5-jet (order x epsilon) t)

(defun putnam-2018-a5-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun putnam-2018-a5-positive-natural-p (value)
  (and
   (natp value)
   (< 0 value)))

(defun putnam-2018-a5-in-bounded-interval-p
    (value bound)
  (and
   (rationalp value)
   (putnam-2018-a5-positive-natural-p bound)
   (<= (- bound) value)
   (<= value bound)))

;; A regular Cauchy name at every natural derivative order and rational point
;; presents a real value rather than restricting that value to the rationals.

(defun-sk putnam-2018-a5-regular-jet-p ()
  (forall (order x epsilon eta)
    (implies
     (and
      (natp order)
      (rationalp x)
      (putnam-2018-a5-positive-rational-p epsilon)
      (putnam-2018-a5-positive-rational-p eta))
     (let ((left
            (putnam-2018-a5-jet order x epsilon))
           (right
            (putnam-2018-a5-jet order x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; Uniform continuity on each compact rational interval is equivalent, after
;; Cauchy completion, to continuity of every represented derivative on R.

(defun-sk putnam-2018-a5-continuity-at-scale-p
    (order bound epsilon delta)
  (forall (x y)
    (implies
     (and
      (putnam-2018-a5-in-bounded-interval-p x bound)
      (putnam-2018-a5-in-bounded-interval-p y bound)
      (< (abs (- x y)) delta))
     (let ((left
            (putnam-2018-a5-jet
             order x (* 1/4 epsilon)))
           (right
            (putnam-2018-a5-jet
             order y (* 1/4 epsilon))))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            epsilon))))))

(defun-sk putnam-2018-a5-continuity-scale-exists-p
    (order bound epsilon)
  (exists (delta)
    (and
     (putnam-2018-a5-positive-rational-p delta)
     (putnam-2018-a5-continuity-at-scale-p
      order bound epsilon delta))))

(defun-sk putnam-2018-a5-compact-continuity-p ()
  (forall (order bound epsilon)
    (implies
     (and
      (natp order)
      (putnam-2018-a5-positive-natural-p bound)
      (putnam-2018-a5-positive-rational-p epsilon))
     (putnam-2018-a5-continuity-scale-exists-p
      order bound epsilon))))

;; For every compact interval and tolerance, one positive rational radius
;; works uniformly for the rational difference quotients. The scaled Cauchy
;; precisions account for division by h and make the next jet level precisely
;; the derivative of the preceding one.

(defun-sk putnam-2018-a5-derivative-at-scale-p
    (order bound epsilon delta)
  (forall (x h)
    (implies
     (and
      (putnam-2018-a5-in-bounded-interval-p x bound)
      (rationalp h)
      (not (equal h 0))
      (putnam-2018-a5-in-bounded-interval-p
       (+ x h) bound)
      (< (abs h) delta))
     (let* ((value-precision
             (* 1/8 epsilon (abs h)))
            (derivative-precision
             (* 1/4 epsilon))
            (right-value
             (putnam-2018-a5-jet
              order (+ x h) value-precision))
            (left-value
             (putnam-2018-a5-jet
              order x value-precision))
            (next-value
             (putnam-2018-a5-jet
              (+ order 1) x derivative-precision)))
       (and
        (rationalp right-value)
        (rationalp left-value)
        (rationalp next-value)
        (<=
         (abs
          (-
           (/ (- right-value left-value) h)
           next-value))
         epsilon))))))

(defun-sk putnam-2018-a5-derivative-scale-exists-p
    (order bound epsilon)
  (exists (delta)
    (and
     (putnam-2018-a5-positive-rational-p delta)
     (putnam-2018-a5-derivative-at-scale-p
      order bound epsilon delta))))

(defun-sk putnam-2018-a5-successive-derivatives-p ()
  (forall (order bound epsilon)
    (implies
     (and
      (natp order)
      (putnam-2018-a5-positive-natural-p bound)
      (putnam-2018-a5-positive-rational-p epsilon))
     (putnam-2018-a5-derivative-scale-exists-p
      order bound epsilon))))

(defun putnam-2018-a5-smooth-jet-p ()
  (and
   (putnam-2018-a5-regular-jet-p)
   (putnam-2018-a5-compact-continuity-p)
   (putnam-2018-a5-successive-derivatives-p)))

;; These all-precision comparisons are equivalent to exact equality of the
;; represented zeroth-order value with EXPECTED.

(defun-sk putnam-2018-a5-point-value-p
    (point expected)
  (forall (epsilon)
    (implies
     (putnam-2018-a5-positive-rational-p epsilon)
     (let ((value
            (putnam-2018-a5-jet
             0 point (* 1/4 epsilon))))
       (and
        (rationalp value)
        (<= (abs (- value expected))
            epsilon))))))

;; For a continuous represented function, this dense rational condition is
;; equivalent to global nonnegativity on the real line.

(defun-sk putnam-2018-a5-nonnegative-p ()
  (forall (x epsilon)
    (implies
     (and
      (rationalp x)
      (putnam-2018-a5-positive-rational-p epsilon))
     (let ((value
            (putnam-2018-a5-jet
             0 x (* 1/4 epsilon))))
       (and
        (rationalp value)
        (<= (- epsilon) value))))))

;; A strict negative value is equivalently witnessed by a positive rational
;; margin. Density and continuity permit the point witness to be rational.

(defun-sk putnam-2018-a5-negative-derivative-exists-p ()
  (exists (order x margin)
    (and
     (natp order)
     (< 0 order)
     (rationalp x)
     (putnam-2018-a5-positive-rational-p margin)
     (let ((value
            (putnam-2018-a5-jet
             order x (* 1/4 margin))))
       (and
        (rationalp value)
        (< (+ value margin) 0))))))

(defun putnambench-putnam-2018-a5-statement ()
  (implies
   (and
    (putnam-2018-a5-smooth-jet-p)
    (putnam-2018-a5-point-value-p 0 0)
    (putnam-2018-a5-point-value-p 1 1)
    (putnam-2018-a5-nonnegative-p))
   (putnam-2018-a5-negative-derivative-exists-p)))

(value-triple :itpeval-statement-checked)
:q
