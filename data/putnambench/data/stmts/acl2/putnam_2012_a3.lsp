;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_a3:
;; the unique continuous real function on [-1,1] satisfying the given
;; functional equation, normalization, and finite left-limit condition is
;; sqrt(1-x^2). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; F-APPROX(x,epsilon) is a rational regular Cauchy name for the value of an
;; arbitrary real function at rational x in [-1,1]. DEFSTUB supplies the
;; source's universal function parameter conservatively, without restricting
;; it to a finite table or an executable APPLY$ object.
;;
;; Continuous functions on the compact interval are represented by uniformly
;; continuous data on its dense rational subset. Every source function has
;; such data, and the data determine a unique continuous extension. Equality
;; and the functional equation are exact Cauchy-name equalities.
;;
;; For the left limit, x=1-t^2 gives sqrt(1-x)=t for t>0. Completeness of the
;; reals makes the Cauchy criterion for f(1-t^2)/t as t approaches 0 from the
;; right equivalent to existence of the source's finite left limit at x=1.
;; All limit and continuity cutoffs remain internally existential.

(defstub putnam-2012-a3-f-approx (x epsilon) t)

(defun putnam-2012-a3-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun putnam-2012-a3-rational-in-unit-interval-p (x)
  (and
   (rationalp x)
   (<= -1 x)
   (<= x 1)))

(defun putnam-2012-a3-isqrt-search
    (radicand candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp radicand))
          (not (natp candidate)))
      0
    (if (<= (* candidate candidate) radicand)
        candidate
      (putnam-2012-a3-isqrt-search
       radicand (- candidate 1)))))

(defun putnam-2012-a3-isqrt (radicand)
  (if (natp radicand)
      (putnam-2012-a3-isqrt-search
       radicand radicand)
    0))

(defun putnam-2012-a3-sqrt-lower (radicand scale)
  (if (and (rationalp radicand)
           (<= 0 radicand)
           (posp scale))
      (/ (putnam-2012-a3-isqrt
          (floor (* radicand scale scale) 1))
         scale)
    0))

;; For positive rational EPSILON, this rational lower approximation is within
;; EPSILON of the principal square root.

(defun putnam-2012-a3-real-sqrt-approx
    (radicand epsilon)
  (if (and (rationalp radicand)
           (<= 0 radicand)
           (putnam-2012-a3-positive-rational-p epsilon))
      (putnam-2012-a3-sqrt-lower
       radicand
       (+ 1 (denominator epsilon)))
    0))

(defun putnam-2012-a3-solution-approx (x epsilon)
  (if (putnam-2012-a3-rational-in-unit-interval-p x)
      (putnam-2012-a3-real-sqrt-approx
       (- 1 (* x x))
       epsilon)
    0))

;; KIND=:SOLUTION selects the displayed closed form. Any other KIND selects
;; the conservative arbitrary-function symbol.

(defun putnam-2012-a3-value (kind x epsilon)
  (if (equal kind :solution)
      (putnam-2012-a3-solution-approx x epsilon)
    (putnam-2012-a3-f-approx x epsilon)))

(defun-sk putnam-2012-a3-regular-cauchy-data-p (kind)
  (forall (x epsilon eta)
    (implies
     (and
      (putnam-2012-a3-rational-in-unit-interval-p x)
      (putnam-2012-a3-positive-rational-p epsilon)
      (putnam-2012-a3-positive-rational-p eta))
     (let ((left
            (putnam-2012-a3-value kind x epsilon))
           (right
            (putnam-2012-a3-value kind x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; This is exact distance <= MARGIN between represented real values.

(defun-sk putnam-2012-a3-value-distance-at-most-p
    (kind x y margin)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2012-a3-positive-rational-p epsilon)
      (putnam-2012-a3-positive-rational-p eta))
     (<=
      (abs
       (-
        (putnam-2012-a3-value kind x epsilon)
        (putnam-2012-a3-value kind y eta)))
      (+ margin epsilon eta)))))

;; Exact distance < EPSILON is expressed by a rational upper margin below it.

(defun-sk putnam-2012-a3-value-distance-below-p
    (kind x y epsilon)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin epsilon)
     (putnam-2012-a3-value-distance-at-most-p
      kind x y margin))))

(defun-sk putnam-2012-a3-uniform-radius-p
    (kind epsilon delta)
  (forall (x y)
    (implies
     (and
      (putnam-2012-a3-rational-in-unit-interval-p x)
      (putnam-2012-a3-rational-in-unit-interval-p y)
      (< (abs (- x y)) delta))
     (putnam-2012-a3-value-distance-below-p
      kind x y epsilon))))

(defun-sk putnam-2012-a3-uniform-radius-exists-p
    (kind epsilon)
  (exists (delta)
    (and
     (putnam-2012-a3-positive-rational-p delta)
     (putnam-2012-a3-uniform-radius-p
      kind epsilon delta))))

(defun-sk putnam-2012-a3-continuous-on-interval-p (kind)
  (forall (epsilon)
    (implies
     (putnam-2012-a3-positive-rational-p epsilon)
     (putnam-2012-a3-uniform-radius-exists-p
      kind epsilon))))

;; Equality in the functional equation is imposed at every rational point.
;; The factor lies in [1/2,1], and its absolute value scales the right-hand
;; Cauchy-name error exactly.

(defun-sk putnam-2012-a3-functional-equation-p (kind)
  (forall (x epsilon eta)
    (implies
     (and
      (putnam-2012-a3-rational-in-unit-interval-p x)
      (putnam-2012-a3-positive-rational-p epsilon)
      (putnam-2012-a3-positive-rational-p eta))
     (let* ((x-square (* x x))
            (two-minus-x-square (- 2 x-square))
            (factor (/ two-minus-x-square 2))
            (transformed-x
             (/ x-square two-minus-x-square))
            (left
             (putnam-2012-a3-value
              kind x epsilon))
            (right
             (* factor
                (putnam-2012-a3-value
                 kind transformed-x eta))))
       (<=
        (abs (- left right))
        (+ epsilon (* (abs factor) eta)))))))

(defun-sk putnam-2012-a3-normalization-p (kind)
  (forall (epsilon)
    (implies
     (putnam-2012-a3-positive-rational-p epsilon)
     (<=
      (abs
       (-
        (putnam-2012-a3-value kind 0 epsilon)
        1))
      epsilon))))

;; For rational t>0, VALUE(kind,1-t^2,epsilon*t)/t approximates
;; f(1-t^2)/t within EPSILON.

(defun-sk putnam-2012-a3-limit-pair-distance-at-most-p
    (kind left-t right-t margin)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2012-a3-positive-rational-p epsilon)
      (putnam-2012-a3-positive-rational-p eta))
     (let* ((left-x (- 1 (* left-t left-t)))
            (right-x (- 1 (* right-t right-t)))
            (left
             (/
              (putnam-2012-a3-value
               kind left-x (* epsilon left-t))
              left-t))
            (right
             (/
              (putnam-2012-a3-value
               kind right-x (* eta right-t))
              right-t)))
       (<=
        (abs (- left right))
        (+ margin epsilon eta))))))

(defun-sk putnam-2012-a3-limit-pair-distance-below-p
    (kind left-t right-t epsilon)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin epsilon)
     (putnam-2012-a3-limit-pair-distance-at-most-p
      kind left-t right-t margin))))

(defun-sk putnam-2012-a3-limit-cauchy-tail-p
    (kind epsilon delta)
  (forall (left-t right-t)
    (implies
     (and
      (putnam-2012-a3-positive-rational-p left-t)
      (putnam-2012-a3-positive-rational-p right-t)
      (< left-t 1)
      (< right-t 1)
      (< left-t delta)
      (< right-t delta))
     (putnam-2012-a3-limit-pair-distance-below-p
      kind left-t right-t epsilon))))

(defun-sk putnam-2012-a3-limit-cauchy-cutoff-exists-p
    (kind epsilon)
  (exists (delta)
    (and
     (putnam-2012-a3-positive-rational-p delta)
     (putnam-2012-a3-limit-cauchy-tail-p
      kind epsilon delta))))

(defun-sk putnam-2012-a3-finite-left-limit-p (kind)
  (forall (epsilon)
    (implies
     (putnam-2012-a3-positive-rational-p epsilon)
     (putnam-2012-a3-limit-cauchy-cutoff-exists-p
      kind epsilon))))

(defun putnam-2012-a3-satisfies-p (kind)
  (and
   (putnam-2012-a3-regular-cauchy-data-p kind)
   (putnam-2012-a3-continuous-on-interval-p kind)
   (putnam-2012-a3-functional-equation-p kind)
   (putnam-2012-a3-normalization-p kind)
   (putnam-2012-a3-finite-left-limit-p kind)))

;; Exact equality on rational points, together with continuity, is equality on
;; every real point of the interval.

(defun-sk putnam-2012-a3-equal-to-solution-p ()
  (forall (x epsilon eta)
    (implies
     (and
      (putnam-2012-a3-rational-in-unit-interval-p x)
      (putnam-2012-a3-positive-rational-p epsilon)
      (putnam-2012-a3-positive-rational-p eta))
     (<=
      (abs
       (-
        (putnam-2012-a3-f-approx x epsilon)
        (putnam-2012-a3-solution-approx x eta)))
      (+ epsilon eta)))))

(defun putnambench-putnam-2012-a3-statement ()
  (and
   (putnam-2012-a3-satisfies-p :solution)
   (implies
    (putnam-2012-a3-satisfies-p :arbitrary)
    (putnam-2012-a3-equal-to-solution-p))))

(value-triple :itpeval-statement-checked)
:q
