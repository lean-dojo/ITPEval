;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_b2:
;; the greatest time for a twice-differentiable real trajectory with
;; nonincreasing second derivative, prescribed displacement s, and endpoint
;; velocities 0 and v is 2*s/v. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive complete real field.  CTX is therefore an arbitrary
;; Dedekind-complete ordered-field presentation, hence the real field up to
;; ordered-field isomorphism.  Tame APPLY$ function objects represent the
;; source sets and real-valued functions.  DEFUN-SK keeps the trajectory,
;; both totalized derivative functions, and every real quantifier internal.
;; Differentiability is the epsilon-remainder definition, while the final two
;; predicates are exactly membership and the upper-bound clause of IsGreatest.

(defun p72b2-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun p72b2-unary (function value)
  (apply$ function (list value)))

(defun p72b2-binary (function left right)
  (apply$ function (list left right)))

(defun-sk p72b2-valid-set-p (carrier set)
  (forall (value)
    (implies
     (apply$ set (list value))
     (p72b2-member-p carrier value))))

(defun-sk p72b2-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p72b2-member-p carrier x)
      (p72b2-member-p carrier y)
      (p72b2-member-p carrier z))
     (and
      (p72b2-member-p
       carrier (p72b2-binary add x y))
      (p72b2-member-p
       carrier (p72b2-binary multiply x y))
      (p72b2-member-p
       carrier (p72b2-unary negate x))
      (p72b2-member-p
       carrier (p72b2-unary inverse x))
      (equal
       (p72b2-binary add (p72b2-binary add x y) z)
       (p72b2-binary add x (p72b2-binary add y z)))
      (equal
       (p72b2-binary add x y)
       (p72b2-binary add y x))
      (equal (p72b2-binary add x zero) x)
      (equal
       (p72b2-binary add x (p72b2-unary negate x))
       zero)
      (equal
       (p72b2-binary
        multiply (p72b2-binary multiply x y) z)
       (p72b2-binary
        multiply x (p72b2-binary multiply y z)))
      (equal
       (p72b2-binary multiply x y)
       (p72b2-binary multiply y x))
      (equal (p72b2-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (p72b2-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p72b2-binary
         multiply x (p72b2-unary inverse x))
        one))
      (equal
       (p72b2-binary
        multiply x (p72b2-binary add y z))
       (p72b2-binary
        add
        (p72b2-binary multiply x y)
        (p72b2-binary multiply x z)))))))

(defun-sk p72b2-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p72b2-member-p carrier x)
      (p72b2-member-p carrier y)
      (p72b2-member-p carrier z))
     (and
      (not (p72b2-binary less x x))
      (or
       (equal x y)
       (p72b2-binary less x y)
       (p72b2-binary less y x))
      (implies
       (and
        (p72b2-binary less x y)
        (p72b2-binary less y z))
       (p72b2-binary less x z))
      (implies
       (p72b2-binary less x y)
       (p72b2-binary
        less
        (p72b2-binary add x z)
        (p72b2-binary add y z)))
      (implies
       (and
        (p72b2-binary less zero x)
        (p72b2-binary less zero y))
       (p72b2-binary
        less zero (p72b2-binary multiply x y)))))))

(defun-sk p72b2-set-nonempty-p (carrier set)
  (exists (value)
    (and
     (p72b2-member-p carrier value)
     (apply$ set (list value)))))

(defun-sk p72b2-upper-bound-p
    (carrier less set bound)
  (forall (value)
    (implies
     (and
      (p72b2-member-p carrier value)
      (apply$ set (list value)))
     (not (p72b2-binary less bound value)))))

(defun-sk p72b2-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p72b2-member-p carrier bound)
     (p72b2-upper-bound-p
      carrier less set bound))))

(defun-sk p72b2-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p72b2-member-p carrier bound)
      (p72b2-upper-bound-p carrier less set bound))
     (not (p72b2-binary less bound supremum)))))

(defun p72b2-supremum-p
    (carrier less set supremum)
  (and
   (p72b2-member-p carrier supremum)
   (p72b2-upper-bound-p carrier less set supremum)
   (p72b2-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p72b2-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p72b2-supremum-p
     carrier less set supremum)))

(defun-sk p72b2-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p72b2-valid-set-p carrier set)
      (p72b2-set-nonempty-p carrier set)
      (p72b2-bounded-above-p carrier less set))
     (p72b2-has-supremum-p carrier less set))))

;; CTX = (carrier zero one add multiply negate inverse less).

(defun p72b2-carrier (ctx) (nth 0 ctx))
(defun p72b2-zero (ctx) (nth 1 ctx))
(defun p72b2-one (ctx) (nth 2 ctx))
(defun p72b2-add (ctx) (nth 3 ctx))
(defun p72b2-multiply (ctx) (nth 4 ctx))
(defun p72b2-negate (ctx) (nth 5 ctx))
(defun p72b2-inverse (ctx) (nth 6 ctx))
(defun p72b2-less (ctx) (nth 7 ctx))

(defun p72b2-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (p72b2-carrier ctx))
   (tamep-functionp (p72b2-add ctx))
   (tamep-functionp (p72b2-multiply ctx))
   (tamep-functionp (p72b2-negate ctx))
   (tamep-functionp (p72b2-inverse ctx))
   (tamep-functionp (p72b2-less ctx))
   (p72b2-member-p
    (p72b2-carrier ctx) (p72b2-zero ctx))
   (p72b2-member-p
    (p72b2-carrier ctx) (p72b2-one ctx))
   (not (equal (p72b2-zero ctx) (p72b2-one ctx)))
   (p72b2-field-laws-p
    (p72b2-carrier ctx)
    (p72b2-zero ctx)
    (p72b2-one ctx)
    (p72b2-add ctx)
    (p72b2-multiply ctx)
    (p72b2-negate ctx)
    (p72b2-inverse ctx))
   (p72b2-order-laws-p
    (p72b2-carrier ctx)
    (p72b2-zero ctx)
    (p72b2-add ctx)
    (p72b2-multiply ctx)
    (p72b2-less ctx))
   (p72b2-binary
    (p72b2-less ctx) (p72b2-zero ctx) (p72b2-one ctx))
   (p72b2-dedekind-complete-p
    (p72b2-carrier ctx) (p72b2-less ctx))))

(defun p72b2-r-add (ctx left right)
  (p72b2-binary (p72b2-add ctx) left right))

(defun p72b2-r-negate (ctx value)
  (p72b2-unary (p72b2-negate ctx) value))

(defun p72b2-r-subtract (ctx left right)
  (p72b2-r-add ctx left (p72b2-r-negate ctx right)))

(defun p72b2-r-multiply (ctx left right)
  (p72b2-binary (p72b2-multiply ctx) left right))

(defun p72b2-r-inverse (ctx value)
  (p72b2-unary (p72b2-inverse ctx) value))

(defun p72b2-r-divide (ctx numerator denominator)
  (p72b2-r-multiply
   ctx numerator (p72b2-r-inverse ctx denominator)))

(defun p72b2-r-less-p (ctx left right)
  (if (p72b2-binary (p72b2-less ctx) left right)
      t nil))

(defun p72b2-r-less-equal-p (ctx left right)
  (not (p72b2-r-less-p ctx right left)))

(defun p72b2-r-absolute (ctx value)
  (if (p72b2-r-less-p ctx value (p72b2-zero ctx))
      (p72b2-r-negate ctx value)
    value))

(defun p72b2-positive-p (ctx value)
  (and
   (p72b2-member-p (p72b2-carrier ctx) value)
   (p72b2-r-less-p ctx (p72b2-zero ctx) value)))

(defun p72b2-two (ctx)
  (p72b2-r-add ctx (p72b2-one ctx) (p72b2-one ctx)))

(defun p72b2-solution-time (ctx s v)
  (p72b2-r-divide
   ctx
   (p72b2-r-multiply ctx (p72b2-two ctx) s)
   v))

(defun p72b2-in-closed-interval-p
    (ctx left right value)
  (and
   (p72b2-member-p (p72b2-carrier ctx) value)
   (p72b2-r-less-equal-p ctx left value)
   (p72b2-r-less-equal-p ctx value right)))

(defun-sk p72b2-real-function-p (ctx function)
  (forall (value)
    (implies
     (p72b2-member-p (p72b2-carrier ctx) value)
     (p72b2-member-p
      (p72b2-carrier ctx)
      (p72b2-unary function value)))))

;; HasDerivAt in epsilon-remainder form:
;; |f(y)-f(x)-d(y-x)| <= epsilon*|y-x| near x.

(defun p72b2-derivative-error
    (ctx function derivative point value)
  (p72b2-r-absolute
   ctx
   (p72b2-r-subtract
    ctx
    (p72b2-r-subtract
     ctx
     (p72b2-unary function value)
     (p72b2-unary function point))
    (p72b2-r-multiply
     ctx derivative
     (p72b2-r-subtract ctx value point)))))

(defun-sk p72b2-global-error-bound-p
    (ctx function derivative point epsilon radius)
  (forall (value)
    (implies
     (and
      (p72b2-member-p (p72b2-carrier ctx) value)
      (p72b2-r-less-p
       ctx
       (p72b2-r-absolute
        ctx (p72b2-r-subtract ctx value point))
       radius))
     (p72b2-r-less-equal-p
      ctx
      (p72b2-derivative-error
       ctx function derivative point value)
      (p72b2-r-multiply
       ctx epsilon
       (p72b2-r-absolute
        ctx (p72b2-r-subtract ctx value point)))))))

(defun-sk p72b2-global-radius-exists-p
    (ctx function derivative point epsilon)
  (exists (radius)
    (and
     (p72b2-positive-p ctx radius)
     (p72b2-global-error-bound-p
      ctx function derivative point epsilon radius))))

(defun-sk p72b2-has-derivative-at-p
    (ctx function derivative point)
  (forall (epsilon)
    (implies
     (p72b2-positive-p ctx epsilon)
     (p72b2-global-radius-exists-p
      ctx function derivative point epsilon))))

(defun-sk p72b2-differentiable-at-p
    (ctx function point)
  (exists (derivative)
    (and
     (p72b2-member-p (p72b2-carrier ctx) derivative)
     (p72b2-has-derivative-at-p
      ctx function derivative point))))

;; This is the source libraries' totalized derivative: the unique derivative
;; at differentiability points, and zero otherwise.

(defun p72b2-deriv-value-p
    (ctx function point value)
  (and
   (p72b2-member-p (p72b2-carrier ctx) value)
   (if (p72b2-differentiable-at-p ctx function point)
       (p72b2-has-derivative-at-p
        ctx function value point)
     (equal value (p72b2-zero ctx)))))

(defun-sk p72b2-deriv-field-values-p
    (ctx function derivative-field)
  (forall (point)
    (implies
     (p72b2-member-p (p72b2-carrier ctx) point)
     (p72b2-deriv-value-p
      ctx function point
      (p72b2-unary derivative-field point)))))

(defun p72b2-deriv-field-p
    (ctx function derivative-field)
  (and
   (tamep-functionp derivative-field)
   (p72b2-real-function-p ctx derivative-field)
   (p72b2-deriv-field-values-p
    ctx function derivative-field)))

;; The Lean source uses ordinary DifferentiableAt, not differentiability
;; relative to the interval. In particular, both endpoints require two-sided
;; derivatives in the ambient real field.
(defun-sk p72b2-differentiable-on-p
    (ctx function left right)
  (forall (point)
    (implies
     (p72b2-in-closed-interval-p ctx left right point)
     (p72b2-differentiable-at-p ctx function point))))

(defun-sk p72b2-antitone-on-p
    (ctx function left right)
  (forall (a b)
    (implies
     (and
      (p72b2-in-closed-interval-p ctx left right a)
      (p72b2-in-closed-interval-p ctx left right b)
      (p72b2-r-less-equal-p ctx a b))
     (p72b2-r-less-equal-p
      ctx
      (p72b2-unary function b)
      (p72b2-unary function a)))))

(defun p72b2-valid-trajectory-p
    (ctx s v time trajectory
         first-derivative second-derivative)
  (and
   (p72b2-member-p (p72b2-carrier ctx) s)
   (p72b2-member-p (p72b2-carrier ctx) v)
   (p72b2-member-p (p72b2-carrier ctx) time)
   (tamep-functionp trajectory)
   (p72b2-real-function-p ctx trajectory)
   (p72b2-deriv-field-p
    ctx trajectory first-derivative)
   (p72b2-deriv-field-p
    ctx first-derivative second-derivative)
   (p72b2-differentiable-on-p
    ctx trajectory (p72b2-zero ctx) time)
   (p72b2-differentiable-on-p
    ctx first-derivative (p72b2-zero ctx) time)
   (p72b2-antitone-on-p
    ctx second-derivative (p72b2-zero ctx) time)
   (equal
    (p72b2-unary first-derivative (p72b2-zero ctx))
    (p72b2-zero ctx))
   (equal
    (p72b2-unary first-derivative time)
    v)
   (equal
    (p72b2-r-subtract
     ctx
     (p72b2-unary trajectory time)
     (p72b2-unary trajectory (p72b2-zero ctx)))
    s)))

(defun-sk p72b2-attainable-p (ctx s v time)
  (exists (trajectory first-derivative second-derivative)
    (p72b2-valid-trajectory-p
     ctx s v time trajectory
     first-derivative second-derivative)))

(defun-sk p72b2-all-attainable-times-bounded-p
    (ctx s v greatest)
  (forall (time)
    (implies
     (and
      (p72b2-member-p (p72b2-carrier ctx) time)
      (p72b2-attainable-p ctx s v time))
     (p72b2-r-less-equal-p ctx time greatest))))

(defun-sk putnambench-putnam-1972-b2-statement ()
  (forall (ctx s v)
    (implies
     (and
      (p72b2-context-p ctx)
      (p72b2-positive-p ctx s)
      (p72b2-positive-p ctx v))
     (let ((greatest (p72b2-solution-time ctx s v)))
       (and
        (p72b2-member-p (p72b2-carrier ctx) greatest)
        (p72b2-attainable-p ctx s v greatest)
        (p72b2-all-attainable-times-bounded-p
         ctx s v greatest))))))

(value-triple :itpeval-statement-checked)
:q
