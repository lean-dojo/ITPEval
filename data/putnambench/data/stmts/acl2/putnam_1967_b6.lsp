;; Statement-only formalization of putnambench corpus artifact putnam_1967_b6:
;; a bounded real-valued function on the unit disk, differentiable in each
;; coordinate, has an interior point where the sum of the squared partial
;; derivatives is at most 16. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the reals as a Dedekind-complete ordered
;; field. The bivariate function is an arbitrary tame APPLY$ function object.
;; All quantifiers below are unbounded ACL2 quantifiers introduced by
;; conservative DEFUN-SK events; no finite carrier or rational restriction is
;; used.

(defun p67b6-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p67b6-unary (operation x)
  (apply$ operation (list x)))

(defun p67b6-binary (operation x y)
  (apply$ operation (list x y)))

(defun p67b6-function-value (function x y)
  (apply$ function (list x y)))

(defun-sk p67b6-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (p67b6-member-p carrier x)
          (p67b6-member-p carrier y)
          (p67b6-member-p carrier z))
     (and
      (p67b6-member-p carrier
                      (p67b6-binary add x y))
      (p67b6-member-p carrier
                      (p67b6-binary multiply x y))
      (p67b6-member-p carrier
                      (p67b6-unary negate x))
      (p67b6-member-p carrier
                      (p67b6-unary inverse x))
      (equal
       (p67b6-binary add (p67b6-binary add x y) z)
       (p67b6-binary add x (p67b6-binary add y z)))
      (equal (p67b6-binary add x y)
             (p67b6-binary add y x))
      (equal (p67b6-binary add x zero) x)
      (equal
       (p67b6-binary add x (p67b6-unary negate x))
       zero)
      (equal
       (p67b6-binary multiply
                       (p67b6-binary multiply x y) z)
       (p67b6-binary multiply
                       x (p67b6-binary multiply y z)))
      (equal (p67b6-binary multiply x y)
             (p67b6-binary multiply y x))
      (equal (p67b6-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (p67b6-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p67b6-binary multiply
                        x (p67b6-unary inverse x))
        one))
      (equal
       (p67b6-binary multiply
                       x (p67b6-binary add y z))
       (p67b6-binary add
                       (p67b6-binary multiply x y)
                       (p67b6-binary multiply x z)))))))

(defun-sk p67b6-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (p67b6-member-p carrier x)
          (p67b6-member-p carrier y)
          (p67b6-member-p carrier z))
     (and
      (not (p67b6-binary less x x))
      (or (equal x y)
          (p67b6-binary less x y)
          (p67b6-binary less y x))
      (implies
       (and (p67b6-binary less x y)
            (p67b6-binary less y z))
       (p67b6-binary less x z))
      (implies
       (p67b6-binary less x y)
       (p67b6-binary
        less
        (p67b6-binary add x z)
        (p67b6-binary add y z)))
      (implies
       (and (p67b6-binary less zero x)
            (p67b6-binary less zero y))
       (p67b6-binary
        less zero (p67b6-binary multiply x y)))))))

(defun-sk p67b6-set-nonempty-p (carrier set)
  (exists (x)
    (and (p67b6-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk p67b6-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (p67b6-member-p carrier x)
          (apply$ set (list x)))
     (not (p67b6-binary less bound x)))))

(defun-sk p67b6-bounded-above-p (carrier less set)
  (exists (bound)
    (and (p67b6-member-p carrier bound)
         (p67b6-upper-bound-p carrier less set bound))))

(defun-sk p67b6-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p67b6-member-p carrier supremum)
     (p67b6-upper-bound-p carrier less set supremum)
     (implies
      (and (p67b6-member-p carrier bound)
           (p67b6-upper-bound-p carrier less set bound))
      (not (p67b6-binary less bound supremum))))))

(defun-sk p67b6-has-supremum-p (carrier less set)
  (exists (supremum)
    (p67b6-supremum-p carrier less set supremum)))

(defun-sk p67b6-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (p67b6-set-nonempty-p carrier set)
          (p67b6-bounded-above-p carrier less set))
     (p67b6-has-supremum-p carrier less set))))

(defun p67b6-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p67b6-member-p carrier zero)
   (p67b6-member-p carrier one)
   (not (equal zero one))
   (p67b6-field-laws-p
    carrier add multiply negate inverse zero one)
   (p67b6-order-laws-p carrier add multiply zero less)
   (p67b6-binary less zero one)
   (p67b6-dedekind-complete-p carrier less)))

(defun p67b6-add (add x y)
  (p67b6-binary add x y))

(defun p67b6-negate (negate x)
  (p67b6-unary negate x))

(defun p67b6-subtract (add negate x y)
  (p67b6-add add x (p67b6-negate negate y)))

(defun p67b6-multiply (multiply x y)
  (p67b6-binary multiply x y))

(defun p67b6-square (multiply x)
  (p67b6-multiply multiply x x))

(defun p67b6-less-p (less x y)
  (if (p67b6-binary less x y) t nil))

(defun p67b6-less-equal-p (less x y)
  (not (p67b6-less-p less y x)))

(defun p67b6-absolute-value (less negate zero x)
  (if (p67b6-less-p less x zero)
      (p67b6-negate negate x)
    x))

(defun p67b6-positive-p (carrier less zero x)
  (and (p67b6-member-p carrier x)
       (p67b6-less-p less zero x)))

(defun p67b6-two (add one)
  (p67b6-add add one one))

(defun p67b6-four (add one)
  (let ((two (p67b6-two add one)))
    (p67b6-add add two two)))

(defun p67b6-eight (add one)
  (let ((four (p67b6-four add one)))
    (p67b6-add add four four)))

(defun p67b6-sixteen (add one)
  (let ((eight (p67b6-eight add one)))
    (p67b6-add add eight eight)))

(defun-sk p67b6-bivariate-real-function-p (carrier function)
  (forall (x y)
    (implies
     (and (p67b6-member-p carrier x)
          (p67b6-member-p carrier y))
     (p67b6-member-p
      carrier (p67b6-function-value function x y)))))

(defun p67b6-valid-bivariate-function-p (carrier function)
  (and (tamep-functionp function)
       (p67b6-bivariate-real-function-p carrier function)))

;; The derivative condition is
;; |f(z,y)-f(x,y)-d(z-x)| <= epsilon |z-x|
;; on a sufficiently small neighborhood. This is the standard real
;; epsilon-remainder characterization of a derivative.

(defun p67b6-x-derivative-residual
    (function add multiply negate x y derivative z)
  (p67b6-subtract
   add negate
   (p67b6-subtract
    add negate
    (p67b6-function-value function z y)
    (p67b6-function-value function x y))
   (p67b6-multiply
    multiply derivative
    (p67b6-subtract add negate z x))))

(defun p67b6-y-derivative-residual
    (function add multiply negate x y derivative z)
  (p67b6-subtract
   add negate
   (p67b6-subtract
    add negate
    (p67b6-function-value function x z)
    (p67b6-function-value function x y))
   (p67b6-multiply
    multiply derivative
    (p67b6-subtract add negate z y))))

(defun-sk p67b6-x-derivative-neighborhood-p
    (carrier function add multiply negate zero less
     x y derivative epsilon delta)
  (forall (z)
    (implies
     (and
      (p67b6-member-p carrier z)
      (p67b6-less-p
       less
       (p67b6-absolute-value
        less negate zero
        (p67b6-subtract add negate z x))
       delta))
     (p67b6-less-equal-p
      less
      (p67b6-absolute-value
       less negate zero
       (p67b6-x-derivative-residual
        function add multiply negate x y derivative z))
      (p67b6-multiply
       multiply epsilon
       (p67b6-absolute-value
        less negate zero
        (p67b6-subtract add negate z x)))))))

(defun-sk p67b6-y-derivative-neighborhood-p
    (carrier function add multiply negate zero less
     x y derivative epsilon delta)
  (forall (z)
    (implies
     (and
      (p67b6-member-p carrier z)
      (p67b6-less-p
       less
       (p67b6-absolute-value
        less negate zero
        (p67b6-subtract add negate z y))
       delta))
     (p67b6-less-equal-p
      less
      (p67b6-absolute-value
       less negate zero
       (p67b6-y-derivative-residual
        function add multiply negate x y derivative z))
      (p67b6-multiply
       multiply epsilon
       (p67b6-absolute-value
        less negate zero
        (p67b6-subtract add negate z y)))))))

(defun-sk p67b6-x-derivative-radius-exists-p
    (carrier function add multiply negate zero less
     x y derivative epsilon)
  (exists (delta)
    (and
     (p67b6-positive-p carrier less zero delta)
     (p67b6-x-derivative-neighborhood-p
      carrier function add multiply negate zero less
      x y derivative epsilon delta))))

(defun-sk p67b6-y-derivative-radius-exists-p
    (carrier function add multiply negate zero less
     x y derivative epsilon)
  (exists (delta)
    (and
     (p67b6-positive-p carrier less zero delta)
     (p67b6-y-derivative-neighborhood-p
      carrier function add multiply negate zero less
      x y derivative epsilon delta))))

(defun-sk p67b6-has-x-derivative-at-p
    (carrier function add multiply negate zero less
     x y derivative)
  (forall (epsilon)
    (implies
     (p67b6-positive-p carrier less zero epsilon)
     (p67b6-x-derivative-radius-exists-p
      carrier function add multiply negate zero less
      x y derivative epsilon))))

(defun-sk p67b6-has-y-derivative-at-p
    (carrier function add multiply negate zero less
     x y derivative)
  (forall (epsilon)
    (implies
     (p67b6-positive-p carrier less zero epsilon)
     (p67b6-y-derivative-radius-exists-p
      carrier function add multiply negate zero less
      x y derivative epsilon))))

(defun p67b6-x-derivative-p
    (carrier function add multiply negate zero less
     x y derivative)
  (and
   (p67b6-member-p carrier x)
   (p67b6-member-p carrier y)
   (p67b6-member-p carrier derivative)
   (p67b6-has-x-derivative-at-p
    carrier function add multiply negate zero less
    x y derivative)))

(defun p67b6-y-derivative-p
    (carrier function add multiply negate zero less
     x y derivative)
  (and
   (p67b6-member-p carrier x)
   (p67b6-member-p carrier y)
   (p67b6-member-p carrier derivative)
   (p67b6-has-y-derivative-at-p
    carrier function add multiply negate zero less
    x y derivative)))

(defun-sk p67b6-x-derivative-exists-at-p
    (carrier function add multiply negate zero less x y)
  (exists (derivative)
    (p67b6-x-derivative-p
     carrier function add multiply negate zero less
     x y derivative)))

(defun-sk p67b6-y-derivative-exists-at-p
    (carrier function add multiply negate zero less x y)
  (exists (derivative)
    (p67b6-y-derivative-p
     carrier function add multiply negate zero less
     x y derivative)))

(defun-sk p67b6-coordinatewise-differentiable-p
    (carrier function add multiply negate zero less)
  (forall (x y)
    (implies
     (and (p67b6-member-p carrier x)
          (p67b6-member-p carrier y))
     (and
      (p67b6-x-derivative-exists-at-p
       carrier function add multiply negate zero less x y)
      (p67b6-y-derivative-exists-at-p
       carrier function add multiply negate zero less x y)))))

(defun p67b6-radius-squared (add multiply x y)
  (p67b6-add
   add
   (p67b6-square multiply x)
   (p67b6-square multiply y)))

(defun-sk p67b6-bounded-on-unit-disk-p
    (carrier function add multiply negate zero one less)
  (forall (x y)
    (implies
     (and
      (p67b6-member-p carrier x)
      (p67b6-member-p carrier y)
      (p67b6-less-equal-p
       less (p67b6-radius-squared add multiply x y) one))
     (p67b6-less-equal-p
      less
      (p67b6-absolute-value
       less negate zero
       (p67b6-function-value function x y))
      one))))

(defun-sk p67b6-interior-small-gradient-point-p
    (carrier function add multiply negate zero one less)
  (exists (x y x-derivative y-derivative)
    (and
     (p67b6-member-p carrier x)
     (p67b6-member-p carrier y)
     (p67b6-x-derivative-p
      carrier function add multiply negate zero less
      x y x-derivative)
     (p67b6-y-derivative-p
      carrier function add multiply negate zero less
      x y y-derivative)
     (p67b6-less-p
      less (p67b6-radius-squared add multiply x y) one)
     (p67b6-less-equal-p
      less
      (p67b6-add
       add
       (p67b6-square multiply x-derivative)
       (p67b6-square multiply y-derivative))
      (p67b6-sixteen add one)))))

(defun putnambench-putnam-1967-b6-statement
    (carrier add multiply negate inverse zero one less function)
  (implies
   (and
    (p67b6-real-field-p
     carrier add multiply negate inverse zero one less)
    (p67b6-valid-bivariate-function-p carrier function)
    (p67b6-coordinatewise-differentiable-p
     carrier function add multiply negate zero less)
    (p67b6-bounded-on-unit-disk-p
     carrier function add multiply negate zero one less))
   (p67b6-interior-small-gradient-point-p
    carrier function add multiply negate zero one less)))

(value-triple :itpeval-statement-checked)
:q
