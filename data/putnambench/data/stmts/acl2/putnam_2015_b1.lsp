;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_b1:
;; a three-times differentiable real function with five distinct real zeros
;; makes f+6f'+12f''+8f''' have two distinct real zeros.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; REAL-APPROX names arbitrary real arguments by regular rational Cauchy
;; approximations. JET-APPROX similarly names f, f', and f'' at orders 0, 1,
;; and 2. THIRD-APPROX names an internally quantified pointwise value of f'''.
;; DEFSTUB supplies only generic function symbols; every analytic property is
;; stated explicitly below by conservative DEFUN-SK predicates.

(defstub putnam-2015-b1-real-approx (name precision) t)
(defstub putnam-2015-b1-jet-approx (order point precision) t)
(defstub putnam-2015-b1-third-approx (name precision) t)

(defun putnam-2015-b1-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun putnam-2015-b1-jet-order-p (order)
  (and
   (natp order)
   (<= order 2)))

;; Regular names represent arbitrary reals, not merely rational values.

(defun-sk putnam-2015-b1-real-name-p (name)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2015-b1-positive-rational-p epsilon)
      (putnam-2015-b1-positive-rational-p eta))
     (let ((left
            (putnam-2015-b1-real-approx name epsilon))
           (right
            (putnam-2015-b1-real-approx name eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun-sk putnam-2015-b1-real-domain-p ()
  (forall (name)
    (putnam-2015-b1-real-name-p name)))

(defun-sk putnam-2015-b1-jet-value-name-p
    (order point)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2015-b1-positive-rational-p epsilon)
      (putnam-2015-b1-positive-rational-p eta))
     (let ((left
            (putnam-2015-b1-jet-approx
             order point epsilon))
           (right
            (putnam-2015-b1-jet-approx
             order point eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

(defun-sk putnam-2015-b1-third-name-p (name)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2015-b1-positive-rational-p epsilon)
      (putnam-2015-b1-positive-rational-p eta))
     (let ((left
            (putnam-2015-b1-third-approx name epsilon))
           (right
            (putnam-2015-b1-third-approx name eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; These predicates are exact equality and strict-distance comparisons of
;; represented real limits.

(defun-sk putnam-2015-b1-real-equal-p (left right)
  (forall (epsilon)
    (implies
     (putnam-2015-b1-positive-rational-p epsilon)
     (<=
      (abs
       (-
        (putnam-2015-b1-real-approx left epsilon)
        (putnam-2015-b1-real-approx right epsilon)))
      (* 2 epsilon)))))

(defun-sk putnam-2015-b1-real-distance-at-most-p
    (left right bound)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2015-b1-positive-rational-p epsilon)
      (putnam-2015-b1-positive-rational-p eta))
     (<=
      (abs
       (-
        (putnam-2015-b1-real-approx left epsilon)
        (putnam-2015-b1-real-approx right eta)))
      (+ bound epsilon eta)))))

(defun-sk putnam-2015-b1-real-distance-below-p
    (left right radius)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin radius)
     (putnam-2015-b1-real-distance-at-most-p
      left right margin))))

(defun-sk putnam-2015-b1-jet-value-equal-p
    (order left right)
  (forall (epsilon)
    (implies
     (putnam-2015-b1-positive-rational-p epsilon)
     (<=
      (abs
       (-
        (putnam-2015-b1-jet-approx
         order left epsilon)
        (putnam-2015-b1-jet-approx
         order right epsilon)))
      (* 2 epsilon)))))

(defun-sk putnam-2015-b1-jet-value-distance-at-most-p
    (order left right bound)
  (forall (epsilon eta)
    (implies
     (and
      (putnam-2015-b1-positive-rational-p epsilon)
      (putnam-2015-b1-positive-rational-p eta))
     (<=
      (abs
       (-
        (putnam-2015-b1-jet-approx
         order left epsilon)
        (putnam-2015-b1-jet-approx
         order right eta)))
      (+ bound epsilon eta)))))

(defun-sk putnam-2015-b1-jet-value-distance-below-p
    (order left right radius)
  (exists (margin)
    (and
     (rationalp margin)
     (<= 0 margin)
     (< margin radius)
     (putnam-2015-b1-jet-value-distance-at-most-p
      order left right margin))))

(defun-sk putnam-2015-b1-regular-jet-p ()
  (forall (order point)
    (implies
     (putnam-2015-b1-jet-order-p order)
     (putnam-2015-b1-jet-value-name-p
      order point))))

(defun-sk putnam-2015-b1-extensional-jet-p ()
  (forall (order left right)
    (implies
     (and
      (putnam-2015-b1-jet-order-p order)
      (putnam-2015-b1-real-equal-p left right))
     (putnam-2015-b1-jet-value-equal-p
      order left right))))

;; Continuity is stated for f, f', and f'' with the usual internal
;; forall-epsilon/exists-delta/forall-point scope.

(defun-sk putnam-2015-b1-continuity-neighborhood-p
    (order point epsilon delta)
  (forall (nearby)
    (implies
     (putnam-2015-b1-real-distance-below-p
      point nearby delta)
     (putnam-2015-b1-jet-value-distance-below-p
      order point nearby epsilon))))

(defun-sk putnam-2015-b1-continuity-radius-exists-p
    (order point epsilon)
  (exists (delta)
    (and
     (putnam-2015-b1-positive-rational-p delta)
     (putnam-2015-b1-continuity-neighborhood-p
      order point epsilon delta))))

(defun-sk putnam-2015-b1-continuous-jet-p ()
  (forall (order point epsilon)
    (implies
     (and
      (putnam-2015-b1-jet-order-p order)
      (putnam-2015-b1-positive-rational-p epsilon))
     (putnam-2015-b1-continuity-radius-exists-p
      order point epsilon))))

;; The following eventual-precision condition is exactly
;;
;; |f_k(y)-f_k(x)-f_{k+1}(x)(y-x)| <= epsilon |y-x|.
;;
;; Expressing it through convergent rational samples avoids restricting real
;; arguments or values to rationals.

(defun-sk putnam-2015-b1-jet-linearization-eventually-p
    (order point nearby epsilon tolerance precision-bound)
  (forall (precision)
    (implies
     (and
      (putnam-2015-b1-positive-rational-p precision)
      (<= precision precision-bound))
     (let* ((at-nearby
             (putnam-2015-b1-jet-approx
              order nearby precision))
            (at-point
             (putnam-2015-b1-jet-approx
              order point precision))
            (derivative
             (putnam-2015-b1-jet-approx
              (+ order 1) point precision))
            (nearby-value
             (putnam-2015-b1-real-approx
              nearby precision))
            (point-value
             (putnam-2015-b1-real-approx
              point precision))
            (increment
             (- nearby-value point-value))
            (residual
             (-
              (- at-nearby at-point)
              (* derivative increment))))
       (and
        (rationalp at-nearby)
        (rationalp at-point)
        (rationalp derivative)
        (rationalp nearby-value)
        (rationalp point-value)
        (<=
         (abs residual)
         (+ (* epsilon (abs increment))
            tolerance)))))))

(defun-sk putnam-2015-b1-jet-linearization-p
    (order point nearby epsilon tolerance)
  (exists (precision-bound)
    (and
     (putnam-2015-b1-positive-rational-p
      precision-bound)
     (<= precision-bound tolerance)
     (putnam-2015-b1-jet-linearization-eventually-p
      order point nearby epsilon tolerance
      precision-bound))))

(defun-sk putnam-2015-b1-jet-linearization-bound-p
    (order point nearby epsilon)
  (forall (tolerance)
    (implies
     (putnam-2015-b1-positive-rational-p tolerance)
     (putnam-2015-b1-jet-linearization-p
      order point nearby epsilon tolerance))))

(defun-sk putnam-2015-b1-derivative-neighborhood-p
    (order point epsilon delta)
  (forall (nearby)
    (implies
     (putnam-2015-b1-real-distance-below-p
      point nearby delta)
     (putnam-2015-b1-jet-linearization-bound-p
      order point nearby epsilon))))

(defun-sk putnam-2015-b1-derivative-radius-exists-p
    (order point epsilon)
  (exists (delta)
    (and
     (putnam-2015-b1-positive-rational-p delta)
     (putnam-2015-b1-derivative-neighborhood-p
      order point epsilon delta))))

(defun-sk putnam-2015-b1-successive-derivatives-p ()
  (forall (order point epsilon)
    (implies
     (and
      (natp order)
      (<= order 1)
      (putnam-2015-b1-positive-rational-p epsilon))
     (putnam-2015-b1-derivative-radius-exists-p
      order point epsilon))))

;; f''' is not assumed continuous. At each point it is an internal regular
;; real witness satisfying the derivative definition for f''.

(defun-sk putnam-2015-b1-third-linearization-eventually-p
    (point nearby third epsilon tolerance precision-bound)
  (forall (precision)
    (implies
     (and
      (putnam-2015-b1-positive-rational-p precision)
      (<= precision precision-bound))
     (let* ((at-nearby
             (putnam-2015-b1-jet-approx
              2 nearby precision))
            (at-point
             (putnam-2015-b1-jet-approx
              2 point precision))
            (derivative
             (putnam-2015-b1-third-approx
              third precision))
            (nearby-value
             (putnam-2015-b1-real-approx
              nearby precision))
            (point-value
             (putnam-2015-b1-real-approx
              point precision))
            (increment
             (- nearby-value point-value))
            (residual
             (-
              (- at-nearby at-point)
              (* derivative increment))))
       (and
        (rationalp at-nearby)
        (rationalp at-point)
        (rationalp derivative)
        (rationalp nearby-value)
        (rationalp point-value)
        (<=
         (abs residual)
         (+ (* epsilon (abs increment))
            tolerance)))))))

(defun-sk putnam-2015-b1-third-linearization-p
    (point nearby third epsilon tolerance)
  (exists (precision-bound)
    (and
     (putnam-2015-b1-positive-rational-p
      precision-bound)
     (<= precision-bound tolerance)
     (putnam-2015-b1-third-linearization-eventually-p
      point nearby third epsilon tolerance
      precision-bound))))

(defun-sk putnam-2015-b1-third-linearization-bound-p
    (point nearby third epsilon)
  (forall (tolerance)
    (implies
     (putnam-2015-b1-positive-rational-p tolerance)
     (putnam-2015-b1-third-linearization-p
      point nearby third epsilon tolerance))))

(defun-sk putnam-2015-b1-third-derivative-neighborhood-p
    (point third epsilon delta)
  (forall (nearby)
    (implies
     (putnam-2015-b1-real-distance-below-p
      point nearby delta)
     (putnam-2015-b1-third-linearization-bound-p
      point nearby third epsilon))))

(defun-sk putnam-2015-b1-third-derivative-radius-exists-p
    (point third epsilon)
  (exists (delta)
    (and
     (putnam-2015-b1-positive-rational-p delta)
     (putnam-2015-b1-third-derivative-neighborhood-p
      point third epsilon delta))))

(defun-sk putnam-2015-b1-third-derivative-at-p
    (point third)
  (forall (epsilon)
    (implies
     (putnam-2015-b1-positive-rational-p epsilon)
     (putnam-2015-b1-third-derivative-radius-exists-p
      point third epsilon))))

(defun-sk putnam-2015-b1-third-derivative-exists-p
    (point)
  (exists (third)
    (and
     (putnam-2015-b1-third-name-p third)
     (putnam-2015-b1-third-derivative-at-p
      point third))))

(defun-sk putnam-2015-b1-third-differentiable-p ()
  (forall (point)
    (putnam-2015-b1-third-derivative-exists-p
     point)))

(defun putnam-2015-b1-smooth-jet-p ()
  (and
   (putnam-2015-b1-real-domain-p)
   (putnam-2015-b1-regular-jet-p)
   (putnam-2015-b1-extensional-jet-p)
   (putnam-2015-b1-continuous-jet-p)
   (putnam-2015-b1-successive-derivatives-p)
   (putnam-2015-b1-third-differentiable-p)))

;; Exact zero predicates use the error modulus of the regular names.

(defun-sk putnam-2015-b1-f-zero-p (point)
  (forall (epsilon)
    (implies
     (putnam-2015-b1-positive-rational-p epsilon)
     (let ((value
            (putnam-2015-b1-jet-approx
             0 point epsilon)))
       (and
        (rationalp value)
        (<= (abs value) epsilon))))))

(defun-sk putnam-2015-b1-five-distinct-zeros-p ()
  (exists (x1 x2 x3 x4 x5)
    (and
     (putnam-2015-b1-f-zero-p x1)
     (putnam-2015-b1-f-zero-p x2)
     (putnam-2015-b1-f-zero-p x3)
     (putnam-2015-b1-f-zero-p x4)
     (putnam-2015-b1-f-zero-p x5)
     (not (putnam-2015-b1-real-equal-p x1 x2))
     (not (putnam-2015-b1-real-equal-p x1 x3))
     (not (putnam-2015-b1-real-equal-p x1 x4))
     (not (putnam-2015-b1-real-equal-p x1 x5))
     (not (putnam-2015-b1-real-equal-p x2 x3))
     (not (putnam-2015-b1-real-equal-p x2 x4))
     (not (putnam-2015-b1-real-equal-p x2 x5))
     (not (putnam-2015-b1-real-equal-p x3 x4))
     (not (putnam-2015-b1-real-equal-p x3 x5))
     (not (putnam-2015-b1-real-equal-p x4 x5)))))

(defun-sk putnam-2015-b1-g-zero-for-third-p
    (point third)
  (forall (epsilon)
    (implies
     (putnam-2015-b1-positive-rational-p epsilon)
     (let* ((precision (/ epsilon 128))
            (base
             (putnam-2015-b1-jet-approx
              0 point precision))
            (first
             (putnam-2015-b1-jet-approx
              1 point precision))
            (second
             (putnam-2015-b1-jet-approx
              2 point precision))
            (third-value
             (putnam-2015-b1-third-approx
              third precision))
            (sum
             (+ base
                (* 6 first)
                (* 12 second)
                (* 8 third-value))))
       (and
        (rationalp base)
        (rationalp first)
        (rationalp second)
        (rationalp third-value)
        (<= (abs sum) epsilon))))))

(defun-sk putnam-2015-b1-g-zero-p (point)
  (exists (third)
    (and
     (putnam-2015-b1-third-name-p third)
     (putnam-2015-b1-third-derivative-at-p
      point third)
     (putnam-2015-b1-g-zero-for-third-p
      point third))))

(defun-sk putnam-2015-b1-two-distinct-g-zeros-p ()
  (exists (x1 x2)
    (and
     (putnam-2015-b1-g-zero-p x1)
     (putnam-2015-b1-g-zero-p x2)
     (not (putnam-2015-b1-real-equal-p x1 x2)))))

(defun putnambench-putnam-2015-b1-statement ()
  (implies
   (and
    (putnam-2015-b1-smooth-jet-p)
    (putnam-2015-b1-five-distinct-zeros-p))
   (putnam-2015-b1-two-distinct-g-zeros-p)))

(value-triple :itpeval-statement-checked)
:q
