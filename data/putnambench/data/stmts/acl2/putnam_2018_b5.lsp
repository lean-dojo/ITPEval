;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_b5:
;; a continuously differentiable map from the real plane to itself, with all
;; four partial derivatives positive and the stated strict Jacobian
;; inequality everywhere, is one-to-one. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the reals as a Dedekind-complete ordered
;; field. The two component functions present an arbitrary map R^2 -> R^2,
;; and DEFUN-SK keeps all four partial-derivative functions and every
;; mathematical quantifier internal to the statement. Continuous Frechet
;; differentiability is expanded below using the max norm on R^2, which is
;; equivalent to the Euclidean norm used by the source.

(defun p18b5-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p18b5-unary (operation x)
  (apply$ operation (list x)))

(defun p18b5-binary (operation x y)
  (apply$ operation (list x y)))

(defun p18b5-function-value (function x y)
  (apply$ function (list x y)))

(defun-sk p18b5-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (p18b5-member-p carrier x)
          (p18b5-member-p carrier y)
          (p18b5-member-p carrier z))
     (and
      (p18b5-member-p carrier
                      (p18b5-binary add x y))
      (p18b5-member-p carrier
                      (p18b5-binary multiply x y))
      (p18b5-member-p carrier
                      (p18b5-unary negate x))
      (p18b5-member-p carrier
                      (p18b5-unary inverse x))
      (equal
       (p18b5-binary add (p18b5-binary add x y) z)
       (p18b5-binary add x (p18b5-binary add y z)))
      (equal (p18b5-binary add x y)
             (p18b5-binary add y x))
      (equal (p18b5-binary add x zero) x)
      (equal
       (p18b5-binary add x (p18b5-unary negate x))
       zero)
      (equal
       (p18b5-binary multiply
                       (p18b5-binary multiply x y) z)
       (p18b5-binary multiply
                       x (p18b5-binary multiply y z)))
      (equal (p18b5-binary multiply x y)
             (p18b5-binary multiply y x))
      (equal (p18b5-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (p18b5-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p18b5-binary multiply
                      x (p18b5-unary inverse x))
        one))
      (equal
       (p18b5-binary multiply
                     x (p18b5-binary add y z))
       (p18b5-binary add
                     (p18b5-binary multiply x y)
                     (p18b5-binary multiply x z)))))))

(defun-sk p18b5-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (p18b5-member-p carrier x)
          (p18b5-member-p carrier y)
          (p18b5-member-p carrier z))
     (and
      (not (p18b5-binary less x x))
      (or (equal x y)
          (p18b5-binary less x y)
          (p18b5-binary less y x))
      (implies
       (and (p18b5-binary less x y)
            (p18b5-binary less y z))
       (p18b5-binary less x z))
      (implies
       (p18b5-binary less x y)
       (p18b5-binary
        less
        (p18b5-binary add x z)
        (p18b5-binary add y z)))
      (implies
       (and (p18b5-binary less zero x)
            (p18b5-binary less zero y))
       (p18b5-binary
        less zero (p18b5-binary multiply x y)))))))

(defun-sk p18b5-set-nonempty-p (carrier set)
  (exists (x)
    (and (p18b5-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk p18b5-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (p18b5-member-p carrier x)
          (apply$ set (list x)))
     (not (p18b5-binary less bound x)))))

(defun-sk p18b5-bounded-above-p (carrier less set)
  (exists (bound)
    (and (p18b5-member-p carrier bound)
         (p18b5-upper-bound-p carrier less set bound))))

(defun-sk p18b5-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p18b5-member-p carrier supremum)
     (p18b5-upper-bound-p carrier less set supremum)
     (implies
      (and (p18b5-member-p carrier bound)
           (p18b5-upper-bound-p carrier less set bound))
      (not (p18b5-binary less bound supremum))))))

(defun-sk p18b5-has-supremum-p (carrier less set)
  (exists (supremum)
    (p18b5-supremum-p carrier less set supremum)))

(defun-sk p18b5-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (p18b5-set-nonempty-p carrier set)
          (p18b5-bounded-above-p carrier less set))
     (p18b5-has-supremum-p carrier less set))))

(defun p18b5-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p18b5-member-p carrier zero)
   (p18b5-member-p carrier one)
   (not (equal zero one))
   (p18b5-field-laws-p
    carrier add multiply negate inverse zero one)
   (p18b5-order-laws-p carrier add multiply zero less)
   (p18b5-binary less zero one)
   (p18b5-dedekind-complete-p carrier less)))

(defun p18b5-add (add x y)
  (p18b5-binary add x y))

(defun p18b5-negate (negate x)
  (p18b5-unary negate x))

(defun p18b5-subtract (add negate x y)
  (p18b5-add add x (p18b5-negate negate y)))

(defun p18b5-multiply (multiply x y)
  (p18b5-binary multiply x y))

(defun p18b5-less-p (less x y)
  (if (p18b5-binary less x y) t nil))

(defun p18b5-less-equal-p (less x y)
  (not (p18b5-less-p less y x)))

(defun p18b5-absolute-value (less negate zero x)
  (if (p18b5-less-p less x zero)
      (p18b5-negate negate x)
    x))

(defun p18b5-positive-p (carrier less zero x)
  (and (p18b5-member-p carrier x)
       (p18b5-less-p less zero x)))

(defun p18b5-max (less x y)
  (if (p18b5-less-p less x y) y x))

(defun p18b5-plane-distance
    (less negate zero x-step y-step)
  (p18b5-max
   less
   (p18b5-absolute-value less negate zero x-step)
   (p18b5-absolute-value less negate zero y-step)))

(defun-sk p18b5-bivariate-real-function-p (carrier function)
  (forall (x y)
    (implies
     (and (p18b5-member-p carrier x)
          (p18b5-member-p carrier y))
     (p18b5-member-p
      carrier (p18b5-function-value function x y)))))

(defun p18b5-valid-bivariate-function-p (carrier function)
  (and (tamep-functionp function)
       (p18b5-bivariate-real-function-p carrier function)))

;; A linear functional on R^2 is represented by its values on (1,0) and
;; (0,1). The following residual condition is the Frechet derivative
;; definition in the max norm.

(defun p18b5-derivative-residual
    (function x-derivative y-derivative
     add multiply negate x y x-step y-step)
  (p18b5-subtract
   add negate
   (p18b5-subtract
    add negate
    (p18b5-function-value
     function
     (p18b5-add add x x-step)
     (p18b5-add add y y-step))
    (p18b5-function-value function x y))
   (p18b5-add
    add
    (p18b5-multiply
     multiply
     (p18b5-function-value x-derivative x y)
     x-step)
    (p18b5-multiply
     multiply
     (p18b5-function-value y-derivative x y)
     y-step))))

(defun-sk p18b5-frechet-neighborhood-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less
     x y epsilon delta)
  (forall (x-step y-step)
    (implies
     (and
      (p18b5-member-p carrier x-step)
      (p18b5-member-p carrier y-step)
      (p18b5-less-p
       less
       (p18b5-plane-distance
        less negate zero x-step y-step)
       delta))
     (p18b5-less-equal-p
      less
      (p18b5-absolute-value
       less negate zero
       (p18b5-derivative-residual
        function x-derivative y-derivative
        add multiply negate x y x-step y-step))
      (p18b5-multiply
       multiply epsilon
       (p18b5-plane-distance
        less negate zero x-step y-step))))))

(defun-sk p18b5-frechet-radius-exists-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less x y epsilon)
  (exists (delta)
    (and
     (p18b5-positive-p carrier less zero delta)
     (p18b5-frechet-neighborhood-p
      carrier function x-derivative y-derivative
      add multiply negate zero less
      x y epsilon delta))))

(defun-sk p18b5-has-frechet-derivative-at-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less x y)
  (forall (epsilon)
    (implies
     (p18b5-positive-p carrier less zero epsilon)
     (p18b5-frechet-radius-exists-p
      carrier function x-derivative y-derivative
      add multiply negate zero less x y epsilon))))

(defun-sk p18b5-everywhere-frechet-differentiable-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less)
  (forall (x y)
    (implies
     (and (p18b5-member-p carrier x)
          (p18b5-member-p carrier y))
     (p18b5-has-frechet-derivative-at-p
      carrier function x-derivative y-derivative
      add multiply negate zero less x y))))

;; Joint continuity of both derivative coordinates is equivalent, in finite
;; dimension, to continuity of the derivative as a continuous linear map.

(defun-sk p18b5-derivative-continuity-neighborhood-p
    (carrier x-derivative y-derivative
     add negate zero less x y epsilon delta)
  (forall (x-step y-step)
    (implies
     (and
      (p18b5-member-p carrier x-step)
      (p18b5-member-p carrier y-step)
      (p18b5-less-p
       less
       (p18b5-plane-distance
        less negate zero x-step y-step)
       delta))
     (and
      (p18b5-less-p
       less
       (p18b5-absolute-value
        less negate zero
        (p18b5-subtract
         add negate
         (p18b5-function-value
          x-derivative
          (p18b5-add add x x-step)
          (p18b5-add add y y-step))
         (p18b5-function-value x-derivative x y)))
       epsilon)
      (p18b5-less-p
       less
       (p18b5-absolute-value
        less negate zero
        (p18b5-subtract
         add negate
         (p18b5-function-value
          y-derivative
          (p18b5-add add x x-step)
          (p18b5-add add y y-step))
         (p18b5-function-value y-derivative x y)))
       epsilon)))))

(defun-sk p18b5-derivative-continuity-radius-exists-p
    (carrier x-derivative y-derivative
     add negate zero less x y epsilon)
  (exists (delta)
    (and
     (p18b5-positive-p carrier less zero delta)
     (p18b5-derivative-continuity-neighborhood-p
      carrier x-derivative y-derivative
      add negate zero less x y epsilon delta))))

(defun-sk p18b5-derivative-pair-continuous-at-p
    (carrier x-derivative y-derivative
     add negate zero less x y)
  (forall (epsilon)
    (implies
     (p18b5-positive-p carrier less zero epsilon)
     (p18b5-derivative-continuity-radius-exists-p
      carrier x-derivative y-derivative
      add negate zero less x y epsilon))))

(defun-sk p18b5-derivative-pair-continuous-p
    (carrier x-derivative y-derivative
     add negate zero less)
  (forall (x y)
    (implies
     (and (p18b5-member-p carrier x)
          (p18b5-member-p carrier y))
     (p18b5-derivative-pair-continuous-at-p
      carrier x-derivative y-derivative
      add negate zero less x y))))

(defun p18b5-continuously-differentiable-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less)
  (and
   (p18b5-valid-bivariate-function-p
    carrier x-derivative)
   (p18b5-valid-bivariate-function-p
    carrier y-derivative)
   (p18b5-everywhere-frechet-differentiable-p
    carrier function x-derivative y-derivative
    add multiply negate zero less)
   (p18b5-derivative-pair-continuous-p
    carrier x-derivative y-derivative
    add negate zero less)))

(defun p18b5-square (multiply x)
  (p18b5-multiply multiply x x))

(defun p18b5-two (add one)
  (p18b5-add add one one))

(defun p18b5-four (add one)
  (let ((two (p18b5-two add one)))
    (p18b5-add add two two)))

(defun p18b5-quarter (add inverse one)
  (p18b5-unary inverse (p18b5-four add one)))

(defun p18b5-jacobian-condition-at-p
    (carrier f1-x f1-y f2-x f2-y
     add multiply negate inverse zero one less x y)
  (let* ((j11 (p18b5-function-value f1-x x y))
         (j12 (p18b5-function-value f1-y x y))
         (j21 (p18b5-function-value f2-x x y))
         (j22 (p18b5-function-value f2-y x y))
         (diagonal-product
          (p18b5-multiply multiply j11 j22))
         (off-diagonal-sum
          (p18b5-add add j12 j21))
         (correction
          (p18b5-multiply
           multiply
           (p18b5-quarter add inverse one)
           (p18b5-square multiply off-diagonal-sum)))
         (gap
          (p18b5-subtract
           add negate diagonal-product correction)))
    (and
     (p18b5-positive-p carrier less zero j11)
     (p18b5-positive-p carrier less zero j12)
     (p18b5-positive-p carrier less zero j21)
     (p18b5-positive-p carrier less zero j22)
     (p18b5-positive-p carrier less zero gap))))

(defun-sk p18b5-jacobian-conditions-p
    (carrier f1-x f1-y f2-x f2-y
     add multiply negate inverse zero one less)
  (forall (x y)
    (implies
     (and (p18b5-member-p carrier x)
          (p18b5-member-p carrier y))
     (p18b5-jacobian-condition-at-p
      carrier f1-x f1-y f2-x f2-y
      add multiply negate inverse zero one less x y))))

;; These four internal witnesses are the uniquely determined coordinate
;; values of the Frechet derivatives of the two component functions.
(defun-sk p18b5-source-hypotheses-p
    (carrier first-component second-component
     add multiply negate inverse zero one less)
  (exists (f1-x f1-y f2-x f2-y)
    (and
     (p18b5-continuously-differentiable-p
      carrier first-component f1-x f1-y
      add multiply negate zero less)
     (p18b5-continuously-differentiable-p
      carrier second-component f2-x f2-y
      add multiply negate zero less)
     (p18b5-jacobian-conditions-p
      carrier f1-x f1-y f2-x f2-y
      add multiply negate inverse zero one less))))

(defun-sk p18b5-injective-p
    (carrier first-component second-component)
  (forall (x1 y1 x2 y2)
    (implies
     (and
      (p18b5-member-p carrier x1)
      (p18b5-member-p carrier y1)
      (p18b5-member-p carrier x2)
      (p18b5-member-p carrier y2)
      (equal
       (p18b5-function-value first-component x1 y1)
       (p18b5-function-value first-component x2 y2))
      (equal
       (p18b5-function-value second-component x1 y1)
       (p18b5-function-value second-component x2 y2)))
     (and (equal x1 x2)
          (equal y1 y2)))))

(defun putnambench-putnam-2018-b5-statement
    (carrier add multiply negate inverse zero one less
     first-component second-component)
  (implies
   (and
    (p18b5-real-field-p
     carrier add multiply negate inverse zero one less)
    (p18b5-valid-bivariate-function-p
     carrier first-component)
    (p18b5-valid-bivariate-function-p
     carrier second-component)
    (p18b5-source-hypotheses-p
     carrier first-component second-component
     add multiply negate inverse zero one less))
   (p18b5-injective-p
    carrier first-component second-component)))

(value-triple :itpeval-statement-checked)
:q
