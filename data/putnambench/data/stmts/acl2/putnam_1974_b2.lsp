;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_b2:
;; a continuously differentiable real function for which (y')^2 + y^3 tends
;; to zero at positive infinity has both y and y' tending to zero there. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A continuous real function is represented by regular rational Cauchy data
;; on rational inputs. Continuity on every bounded interval gives a unique
;; extension to all real inputs. All bounds, precisions, and cutoffs below are
;; unbounded internal quantifiers.

(defun p74b2-value (function x precision)
  (apply$ function (list x precision)))

(defun p74b2-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun p74b2-positive-natural-p (x)
  (and (natp x)
       (< 0 x)))

(defun p74b2-abs (x)
  (if (< x 0) (- x) x))

(defun p74b2-in-bounded-interval-p (x bound)
  (and (<= (- bound) x)
       (<= x bound)))

(defun-sk p74b2-cauchy-values-p (function)
  (forall (x epsilon eta)
    (implies
     (and
      (rationalp x)
      (p74b2-positive-rational-p epsilon)
      (p74b2-positive-rational-p eta))
     (and
      (rationalp (p74b2-value function x epsilon))
      (rationalp (p74b2-value function x eta))
      (<=
       (p74b2-abs
        (-
         (p74b2-value function x epsilon)
         (p74b2-value function x eta)))
       (+ epsilon eta))))))

(defun-sk p74b2-continuity-neighborhood-p
    (function bound epsilon delta)
  (forall (x z)
    (implies
     (and
      (p74b2-positive-natural-p bound)
      (rationalp x)
      (rationalp z)
      (p74b2-in-bounded-interval-p x bound)
      (p74b2-in-bounded-interval-p z bound)
      (p74b2-positive-rational-p epsilon)
      (p74b2-positive-rational-p delta)
      (< (p74b2-abs (- x z)) delta))
     (<=
      (p74b2-abs
       (-
        (p74b2-value function x (* 1/8 epsilon))
        (p74b2-value function z (* 1/8 epsilon))))
      (* 1/2 epsilon)))))

(defun-sk p74b2-continuity-delta-exists-p
    (function bound epsilon)
  (exists (delta)
    (and
     (p74b2-positive-rational-p delta)
     (p74b2-continuity-neighborhood-p
      function bound epsilon delta))))

(defun-sk p74b2-continuous-values-p (function)
  (forall (bound epsilon)
    (implies
     (and
      (p74b2-positive-natural-p bound)
      (p74b2-positive-rational-p epsilon))
     (p74b2-continuity-delta-exists-p
      function bound epsilon))))

(defun p74b2-continuous-real-function-p (function)
  (and
   (tamep-functionp function)
   (p74b2-cauchy-values-p function)
   (p74b2-continuous-values-p function)))

;; Uniform convergence of difference quotients on each bounded interval is
;; equivalent here to having a continuous derivative. The function samples
;; use precision proportional to |h|, so division by h preserves the stated
;; error tolerance.

(defun-sk p74b2-derivative-neighborhood-p
    (function derivative bound epsilon delta)
  (forall (x h)
    (implies
     (and
      (p74b2-positive-natural-p bound)
      (rationalp x)
      (p74b2-in-bounded-interval-p x bound)
      (rationalp h)
      (not (equal h 0))
      (p74b2-positive-rational-p epsilon)
      (p74b2-positive-rational-p delta)
      (< (p74b2-abs h) delta))
     (let* ((function-precision
             (* (p74b2-abs h) (* 1/16 epsilon)))
            (shifted-value
             (p74b2-value
              function (+ x h) function-precision))
            (value
             (p74b2-value function x function-precision))
            (difference-quotient
             (* (- shifted-value value) (/ h)))
            (derivative-value
             (p74b2-value derivative x (* 1/8 epsilon))))
       (<=
        (p74b2-abs
         (- difference-quotient derivative-value))
        (* 1/2 epsilon))))))

(defun-sk p74b2-derivative-delta-exists-p
    (function derivative bound epsilon)
  (exists (delta)
    (and
     (p74b2-positive-rational-p delta)
     (p74b2-derivative-neighborhood-p
      function derivative bound epsilon delta))))

(defun-sk p74b2-derivative-convergence-p
    (function derivative)
  (forall (bound epsilon)
    (implies
     (and
      (p74b2-positive-natural-p bound)
      (p74b2-positive-rational-p epsilon))
     (p74b2-derivative-delta-exists-p
      function derivative bound epsilon))))

(defun p74b2-derivative-candidate-p (function derivative)
  (and
   (p74b2-continuous-real-function-p function)
   (p74b2-continuous-real-function-p derivative)
   (p74b2-derivative-convergence-p function derivative)))

;; The derivative is unique. DEFCHOOSE conservatively selects that internally
;; characterized function and does not add a derivative parameter to the
;; source statement.

(defchoose p74b2-derivative-function
    (derivative)
    (function)
  (p74b2-derivative-candidate-p function derivative))

(defun p74b2-c1-p (function)
  (p74b2-derivative-candidate-p
   function
   (p74b2-derivative-function function)))

;; A Cauchy-named value is at most EPSILON in absolute value exactly when all
;; sufficiently precise rational samples satisfy that closed bound. Requiring
;; this for every positive EPSILON is the usual zero-limit condition.

(defun-sk p74b2-value-small-tail-p
    (function x epsilon precision-bound)
  (forall (precision)
    (implies
     (and
      (p74b2-positive-rational-p precision)
      (< precision precision-bound))
     (<=
      (p74b2-abs
       (p74b2-value function x precision))
      epsilon))))

(defun-sk p74b2-value-small-p (function x epsilon)
  (exists (precision-bound)
    (and
     (p74b2-positive-rational-p precision-bound)
     (p74b2-value-small-tail-p
      function x epsilon precision-bound))))

(defun-sk p74b2-zero-limit-tail-p
    (function epsilon cutoff)
  (forall (x)
    (implies
     (and
      (rationalp x)
      (< cutoff x))
     (p74b2-value-small-p function x epsilon))))

(defun-sk p74b2-zero-limit-cutoff-exists-p
    (function epsilon)
  (exists (cutoff)
    (and
     (rationalp cutoff)
     (p74b2-zero-limit-tail-p
      function epsilon cutoff))))

(defun-sk p74b2-tends-to-zero-at-infinity-p (function)
  (forall (epsilon)
    (implies
     (p74b2-positive-rational-p epsilon)
     (p74b2-zero-limit-cutoff-exists-p
      function epsilon))))

;; The hypothesis uses the same Cauchy semantics for
;; (derivative(x))^2 + (function(x))^3.

(defun p74b2-expression-sample
    (function derivative x precision)
  (let ((y (p74b2-value function x precision))
        (dy (p74b2-value derivative x precision)))
    (+ (* dy dy)
       (* y (* y y)))))

(defun-sk p74b2-expression-small-tail-p
    (function derivative x epsilon precision-bound)
  (forall (precision)
    (implies
     (and
      (p74b2-positive-rational-p precision)
      (< precision precision-bound))
     (<=
      (p74b2-abs
       (p74b2-expression-sample
        function derivative x precision))
      epsilon))))

(defun-sk p74b2-expression-small-p
    (function derivative x epsilon)
  (exists (precision-bound)
    (and
     (p74b2-positive-rational-p precision-bound)
     (p74b2-expression-small-tail-p
      function derivative x epsilon precision-bound))))

(defun-sk p74b2-expression-limit-tail-p
    (function derivative epsilon cutoff)
  (forall (x)
    (implies
     (and
      (rationalp x)
      (< cutoff x))
     (p74b2-expression-small-p
      function derivative x epsilon))))

(defun-sk p74b2-expression-limit-cutoff-exists-p
    (function derivative epsilon)
  (exists (cutoff)
    (and
     (rationalp cutoff)
     (p74b2-expression-limit-tail-p
      function derivative epsilon cutoff))))

(defun-sk p74b2-expression-tends-to-zero-at-infinity-p
    (function derivative)
  (forall (epsilon)
    (implies
     (p74b2-positive-rational-p epsilon)
     (p74b2-expression-limit-cutoff-exists-p
      function derivative epsilon))))

(defun putnambench-putnam-1974-b2-statement (y)
  (let ((dy (p74b2-derivative-function y)))
    (implies
     (and
      (p74b2-c1-p y)
      (p74b2-expression-tends-to-zero-at-infinity-p
       y dy))
     (and
      (p74b2-tends-to-zero-at-infinity-p y)
      (p74b2-tends-to-zero-at-infinity-p dy)))))

(value-triple :itpeval-statement-checked)
:q
