;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_a3:
;; a bounded continuously differentiable real-valued function on the real
;; plane satisfying a constant-coefficient first-order linear PDE is
;; identically zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the reals as a Dedekind-complete ordered
;; field. Functions on the real plane are unbounded tame APPLY$ function
;; objects, and DEFUN-SK keeps the derivative functions and every mathematical
;; quantifier internal to the statement. Continuous Frechet differentiability
;; is expanded below using the max norm on R^2, which is equivalent to the
;; Euclidean norm used by the source.

(defun p10a3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p10a3-unary (operation x)
  (apply$ operation (list x)))

(defun p10a3-binary (operation x y)
  (apply$ operation (list x y)))

(defun p10a3-function-value (function x y)
  (apply$ function (list x y)))

(defun-sk p10a3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y)
          (p10a3-member-p carrier z))
     (and
      (p10a3-member-p carrier
                      (p10a3-binary add x y))
      (p10a3-member-p carrier
                      (p10a3-binary multiply x y))
      (p10a3-member-p carrier
                      (p10a3-unary negate x))
      (p10a3-member-p carrier
                      (p10a3-unary inverse x))
      (equal
       (p10a3-binary add (p10a3-binary add x y) z)
       (p10a3-binary add x (p10a3-binary add y z)))
      (equal (p10a3-binary add x y)
             (p10a3-binary add y x))
      (equal (p10a3-binary add x zero) x)
      (equal
       (p10a3-binary add x (p10a3-unary negate x))
       zero)
      (equal
       (p10a3-binary multiply
                       (p10a3-binary multiply x y) z)
       (p10a3-binary multiply
                       x (p10a3-binary multiply y z)))
      (equal (p10a3-binary multiply x y)
             (p10a3-binary multiply y x))
      (equal (p10a3-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (p10a3-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p10a3-binary multiply
                      x (p10a3-unary inverse x))
        one))
      (equal
       (p10a3-binary multiply
                     x (p10a3-binary add y z))
       (p10a3-binary add
                     (p10a3-binary multiply x y)
                     (p10a3-binary multiply x z)))))))

(defun-sk p10a3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y)
          (p10a3-member-p carrier z))
     (and
      (not (p10a3-binary less x x))
      (or (equal x y)
          (p10a3-binary less x y)
          (p10a3-binary less y x))
      (implies
       (and (p10a3-binary less x y)
            (p10a3-binary less y z))
       (p10a3-binary less x z))
      (implies
       (p10a3-binary less x y)
       (p10a3-binary
        less
        (p10a3-binary add x z)
        (p10a3-binary add y z)))
      (implies
       (and (p10a3-binary less zero x)
            (p10a3-binary less zero y))
       (p10a3-binary
        less zero (p10a3-binary multiply x y)))))))

(defun-sk p10a3-set-nonempty-p (carrier set)
  (exists (x)
    (and (p10a3-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk p10a3-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (p10a3-member-p carrier x)
          (apply$ set (list x)))
     (not (p10a3-binary less bound x)))))

(defun-sk p10a3-bounded-above-p (carrier less set)
  (exists (bound)
    (and (p10a3-member-p carrier bound)
         (p10a3-upper-bound-p carrier less set bound))))

(defun-sk p10a3-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p10a3-member-p carrier supremum)
     (p10a3-upper-bound-p carrier less set supremum)
     (implies
      (and (p10a3-member-p carrier bound)
           (p10a3-upper-bound-p carrier less set bound))
      (not (p10a3-binary less bound supremum))))))

(defun-sk p10a3-has-supremum-p (carrier less set)
  (exists (supremum)
    (p10a3-supremum-p carrier less set supremum)))

(defun-sk p10a3-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (p10a3-set-nonempty-p carrier set)
          (p10a3-bounded-above-p carrier less set))
     (p10a3-has-supremum-p carrier less set))))

(defun p10a3-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p10a3-member-p carrier zero)
   (p10a3-member-p carrier one)
   (not (equal zero one))
   (p10a3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p10a3-order-laws-p carrier add multiply zero less)
   (p10a3-binary less zero one)
   (p10a3-dedekind-complete-p carrier less)))

(defun p10a3-add (add x y)
  (p10a3-binary add x y))

(defun p10a3-negate (negate x)
  (p10a3-unary negate x))

(defun p10a3-subtract (add negate x y)
  (p10a3-add add x (p10a3-negate negate y)))

(defun p10a3-multiply (multiply x y)
  (p10a3-binary multiply x y))

(defun p10a3-less-p (less x y)
  (if (p10a3-binary less x y) t nil))

(defun p10a3-less-equal-p (less x y)
  (not (p10a3-less-p less y x)))

(defun p10a3-absolute-value (less negate zero x)
  (if (p10a3-less-p less x zero)
      (p10a3-negate negate x)
    x))

(defun p10a3-positive-p (carrier less zero x)
  (and (p10a3-member-p carrier x)
       (p10a3-less-p less zero x)))

(defun p10a3-max (less x y)
  (if (p10a3-less-p less x y) y x))

(defun p10a3-plane-distance
    (less negate zero x-step y-step)
  (p10a3-max
   less
   (p10a3-absolute-value less negate zero x-step)
   (p10a3-absolute-value less negate zero y-step)))

(defun-sk p10a3-bivariate-real-function-p (carrier function)
  (forall (x y)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y))
     (p10a3-member-p
      carrier (p10a3-function-value function x y)))))

(defun p10a3-valid-bivariate-function-p (carrier function)
  (and (tamep-functionp function)
       (p10a3-bivariate-real-function-p carrier function)))

;; A linear functional on R^2 is represented by its values on (1,0) and
;; (0,1). The following residual condition is the Frechet derivative
;; definition in the max norm.

(defun p10a3-derivative-residual
    (function x-derivative y-derivative
     add multiply negate x y x-step y-step)
  (p10a3-subtract
   add negate
   (p10a3-subtract
    add negate
    (p10a3-function-value
     function
     (p10a3-add add x x-step)
     (p10a3-add add y y-step))
    (p10a3-function-value function x y))
   (p10a3-add
    add
    (p10a3-multiply
     multiply
     (p10a3-function-value x-derivative x y)
     x-step)
    (p10a3-multiply
     multiply
     (p10a3-function-value y-derivative x y)
     y-step))))

(defun-sk p10a3-frechet-neighborhood-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less
     x y epsilon delta)
  (forall (x-step y-step)
    (implies
     (and
      (p10a3-member-p carrier x-step)
      (p10a3-member-p carrier y-step)
      (p10a3-less-p
       less
       (p10a3-plane-distance
        less negate zero x-step y-step)
       delta))
     (p10a3-less-equal-p
      less
      (p10a3-absolute-value
       less negate zero
       (p10a3-derivative-residual
        function x-derivative y-derivative
        add multiply negate x y x-step y-step))
      (p10a3-multiply
       multiply epsilon
       (p10a3-plane-distance
        less negate zero x-step y-step))))))

(defun-sk p10a3-frechet-radius-exists-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less x y epsilon)
  (exists (delta)
    (and
     (p10a3-positive-p carrier less zero delta)
     (p10a3-frechet-neighborhood-p
      carrier function x-derivative y-derivative
      add multiply negate zero less
      x y epsilon delta))))

(defun-sk p10a3-has-frechet-derivative-at-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less x y)
  (forall (epsilon)
    (implies
     (p10a3-positive-p carrier less zero epsilon)
     (p10a3-frechet-radius-exists-p
      carrier function x-derivative y-derivative
      add multiply negate zero less x y epsilon))))

(defun-sk p10a3-everywhere-frechet-differentiable-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less)
  (forall (x y)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y))
     (p10a3-has-frechet-derivative-at-p
      carrier function x-derivative y-derivative
      add multiply negate zero less x y))))

;; Joint continuity of both derivative coordinates is equivalent, in finite
;; dimension, to continuity of the derivative as a continuous linear map.

(defun-sk p10a3-derivative-continuity-neighborhood-p
    (carrier x-derivative y-derivative
     add negate zero less x y epsilon delta)
  (forall (x-step y-step)
    (implies
     (and
      (p10a3-member-p carrier x-step)
      (p10a3-member-p carrier y-step)
      (p10a3-less-p
       less
       (p10a3-plane-distance
        less negate zero x-step y-step)
       delta))
     (and
      (p10a3-less-p
       less
       (p10a3-absolute-value
        less negate zero
        (p10a3-subtract
         add negate
         (p10a3-function-value
          x-derivative
          (p10a3-add add x x-step)
          (p10a3-add add y y-step))
         (p10a3-function-value x-derivative x y)))
       epsilon)
      (p10a3-less-p
       less
       (p10a3-absolute-value
        less negate zero
        (p10a3-subtract
         add negate
         (p10a3-function-value
          y-derivative
          (p10a3-add add x x-step)
          (p10a3-add add y y-step))
         (p10a3-function-value y-derivative x y)))
       epsilon)))))

(defun-sk p10a3-derivative-continuity-radius-exists-p
    (carrier x-derivative y-derivative
     add negate zero less x y epsilon)
  (exists (delta)
    (and
     (p10a3-positive-p carrier less zero delta)
     (p10a3-derivative-continuity-neighborhood-p
      carrier x-derivative y-derivative
      add negate zero less x y epsilon delta))))

(defun-sk p10a3-derivative-pair-continuous-at-p
    (carrier x-derivative y-derivative
     add negate zero less x y)
  (forall (epsilon)
    (implies
     (p10a3-positive-p carrier less zero epsilon)
     (p10a3-derivative-continuity-radius-exists-p
      carrier x-derivative y-derivative
      add negate zero less x y epsilon))))

(defun-sk p10a3-derivative-pair-continuous-p
    (carrier x-derivative y-derivative
     add negate zero less)
  (forall (x y)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y))
     (p10a3-derivative-pair-continuous-at-p
      carrier x-derivative y-derivative
      add negate zero less x y))))

(defun p10a3-continuously-differentiable-p
    (carrier function x-derivative y-derivative
     add multiply negate zero less)
  (and
   (p10a3-valid-bivariate-function-p
    carrier x-derivative)
   (p10a3-valid-bivariate-function-p
    carrier y-derivative)
   (p10a3-everywhere-frechet-differentiable-p
    carrier function x-derivative y-derivative
    add multiply negate zero less)
   (p10a3-derivative-pair-continuous-p
    carrier x-derivative y-derivative
    add negate zero less)))

(defun-sk p10a3-pde-p
    (carrier function x-derivative y-derivative
     add multiply a b)
  (forall (x y)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y))
     (equal
      (p10a3-function-value function x y)
      (p10a3-add
       add
       (p10a3-multiply
        multiply a
        (p10a3-function-value x-derivative x y))
       (p10a3-multiply
        multiply b
        (p10a3-function-value y-derivative x y)))))))

(defun-sk p10a3-globally-bounded-p
    (carrier function negate zero less bound)
  (forall (x y)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y))
     (p10a3-less-equal-p
      less
      (p10a3-absolute-value
       less negate zero
       (p10a3-function-value function x y))
      bound))))

;; The derivative pair is an internal witness for the derivative already
;; determined uniquely by the Frechet condition. Thus the PDE below refers to
;; exactly the source fderiv values on the two coordinate basis vectors.

(defun-sk p10a3-source-hypotheses-p
    (carrier function add multiply negate zero less a b bound)
  (exists (x-derivative y-derivative)
    (and
     (p10a3-continuously-differentiable-p
      carrier function x-derivative y-derivative
      add multiply negate zero less)
     (p10a3-pde-p
      carrier function x-derivative y-derivative
      add multiply a b)
     (p10a3-globally-bounded-p
      carrier function negate zero less bound))))

(defun-sk p10a3-identically-zero-p
    (carrier function zero)
  (forall (x y)
    (implies
     (and (p10a3-member-p carrier x)
          (p10a3-member-p carrier y))
     (equal (p10a3-function-value function x y)
            zero))))

(defun putnambench-putnam-2010-a3-statement
    (carrier add multiply negate inverse zero one less
     function a b bound)
  (implies
   (and
    (p10a3-real-field-p
     carrier add multiply negate inverse zero one less)
    (p10a3-valid-bivariate-function-p carrier function)
    (p10a3-member-p carrier a)
    (p10a3-member-p carrier b)
    (p10a3-member-p carrier bound)
    (p10a3-source-hypotheses-p
     carrier function add multiply negate zero less
     a b bound))
   (p10a3-identically-zero-p carrier function zero)))

(value-triple :itpeval-statement-checked)
:q
