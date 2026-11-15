;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_b4:
;; a twice differentiable real function with prescribed displacement, zero
;; endpoint velocities, and bounded speed has second derivative of magnitude
;; at least 9/2 somewhere on the unit interval. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive complete real field.  CTX is therefore an arbitrary
;; Dedekind-complete ordered-field presentation, which is uniquely isomorphic
;; to the real field.  Tame APPLY$ function objects represent arbitrary sets
;; and functions.  The derivative predicates below expand the epsilon
;; remainder definition, and DERIV-VALUE-P exactly totalizes the derivative to
;; zero at nondifferentiable points, as in the source libraries.
;;
;; The final predicate rules out an internally quantified counterexample.
;; Thus the derivative functions and the point in the source conclusion retain
;; their original quantifier scopes; none is exposed as a statement parameter.

(defun putnam-1970-b4-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun putnam-1970-b4-unary (function value)
  (apply$ function (list value)))

(defun putnam-1970-b4-binary (function left right)
  (apply$ function (list left right)))

(defun-sk putnam-1970-b4-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1970-b4-member-p carrier x)
      (putnam-1970-b4-member-p carrier y)
      (putnam-1970-b4-member-p carrier z))
     (and
      (putnam-1970-b4-member-p
       carrier (putnam-1970-b4-binary add x y))
      (putnam-1970-b4-member-p
       carrier (putnam-1970-b4-binary multiply x y))
      (putnam-1970-b4-member-p
       carrier (putnam-1970-b4-unary negate x))
      (putnam-1970-b4-member-p
       carrier (putnam-1970-b4-unary inverse x))
      (equal
       (putnam-1970-b4-binary
        add (putnam-1970-b4-binary add x y) z)
       (putnam-1970-b4-binary
        add x (putnam-1970-b4-binary add y z)))
      (equal
       (putnam-1970-b4-binary add x y)
       (putnam-1970-b4-binary add y x))
      (equal (putnam-1970-b4-binary add x zero) x)
      (equal
       (putnam-1970-b4-binary
        add x (putnam-1970-b4-unary negate x))
       zero)
      (equal
       (putnam-1970-b4-binary
        multiply (putnam-1970-b4-binary multiply x y) z)
       (putnam-1970-b4-binary
        multiply x (putnam-1970-b4-binary multiply y z)))
      (equal
       (putnam-1970-b4-binary multiply x y)
       (putnam-1970-b4-binary multiply y x))
      (equal (putnam-1970-b4-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (putnam-1970-b4-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (putnam-1970-b4-binary
         multiply x (putnam-1970-b4-unary inverse x))
        one))
      (equal
       (putnam-1970-b4-binary
        multiply x (putnam-1970-b4-binary add y z))
       (putnam-1970-b4-binary
        add
        (putnam-1970-b4-binary multiply x y)
        (putnam-1970-b4-binary multiply x z)))))))

(defun-sk putnam-1970-b4-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1970-b4-member-p carrier x)
      (putnam-1970-b4-member-p carrier y)
      (putnam-1970-b4-member-p carrier z))
     (and
      (not (putnam-1970-b4-binary less x x))
      (or
       (equal x y)
       (putnam-1970-b4-binary less x y)
       (putnam-1970-b4-binary less y x))
      (implies
       (and
        (putnam-1970-b4-binary less x y)
        (putnam-1970-b4-binary less y z))
       (putnam-1970-b4-binary less x z))
      (implies
       (putnam-1970-b4-binary less x y)
       (putnam-1970-b4-binary
        less
        (putnam-1970-b4-binary add x z)
        (putnam-1970-b4-binary add y z)))
      (implies
       (and
        (putnam-1970-b4-binary less zero x)
        (putnam-1970-b4-binary less zero y))
       (putnam-1970-b4-binary
        less zero
        (putnam-1970-b4-binary multiply x y)))))))

(defun-sk putnam-1970-b4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1970-b4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1970-b4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1970-b4-member-p carrier x)
      (apply$ set (list x)))
     (not (putnam-1970-b4-binary less bound x)))))

(defun-sk putnam-1970-b4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1970-b4-member-p carrier bound)
     (putnam-1970-b4-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1970-b4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (putnam-1970-b4-member-p carrier bound)
      (putnam-1970-b4-upper-bound-p
       carrier less set bound))
     (not
      (putnam-1970-b4-binary less bound supremum)))))

(defun putnam-1970-b4-supremum-p
    (carrier less set supremum)
  (and
   (putnam-1970-b4-member-p carrier supremum)
   (putnam-1970-b4-upper-bound-p
    carrier less set supremum)
   (putnam-1970-b4-least-upper-bound-p
    carrier less set supremum)))

(defun-sk putnam-1970-b4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1970-b4-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1970-b4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1970-b4-set-nonempty-p carrier set)
      (putnam-1970-b4-bounded-above-p
       carrier less set))
     (putnam-1970-b4-has-supremum-p
      carrier less set))))

;; CTX = (carrier zero one add multiply negate inverse less).

(defun putnam-1970-b4-carrier (ctx) (nth 0 ctx))
(defun putnam-1970-b4-zero (ctx) (nth 1 ctx))
(defun putnam-1970-b4-one (ctx) (nth 2 ctx))
(defun putnam-1970-b4-add (ctx) (nth 3 ctx))
(defun putnam-1970-b4-multiply (ctx) (nth 4 ctx))
(defun putnam-1970-b4-negate (ctx) (nth 5 ctx))
(defun putnam-1970-b4-inverse (ctx) (nth 6 ctx))
(defun putnam-1970-b4-less (ctx) (nth 7 ctx))

(defun putnam-1970-b4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (putnam-1970-b4-carrier ctx))
   (tamep-functionp (putnam-1970-b4-add ctx))
   (tamep-functionp (putnam-1970-b4-multiply ctx))
   (tamep-functionp (putnam-1970-b4-negate ctx))
   (tamep-functionp (putnam-1970-b4-inverse ctx))
   (tamep-functionp (putnam-1970-b4-less ctx))
   (putnam-1970-b4-member-p
    (putnam-1970-b4-carrier ctx)
    (putnam-1970-b4-zero ctx))
   (putnam-1970-b4-member-p
    (putnam-1970-b4-carrier ctx)
    (putnam-1970-b4-one ctx))
   (not
    (equal
     (putnam-1970-b4-zero ctx)
     (putnam-1970-b4-one ctx)))
   (putnam-1970-b4-field-laws-p
    (putnam-1970-b4-carrier ctx)
    (putnam-1970-b4-zero ctx)
    (putnam-1970-b4-one ctx)
    (putnam-1970-b4-add ctx)
    (putnam-1970-b4-multiply ctx)
    (putnam-1970-b4-negate ctx)
    (putnam-1970-b4-inverse ctx))
   (putnam-1970-b4-order-laws-p
    (putnam-1970-b4-carrier ctx)
    (putnam-1970-b4-zero ctx)
    (putnam-1970-b4-add ctx)
    (putnam-1970-b4-multiply ctx)
    (putnam-1970-b4-less ctx))
   (putnam-1970-b4-binary
    (putnam-1970-b4-less ctx)
    (putnam-1970-b4-zero ctx)
    (putnam-1970-b4-one ctx))
   (putnam-1970-b4-dedekind-complete-p
    (putnam-1970-b4-carrier ctx)
    (putnam-1970-b4-less ctx))))

(defun putnam-1970-b4-r-add (ctx left right)
  (putnam-1970-b4-binary
   (putnam-1970-b4-add ctx) left right))

(defun putnam-1970-b4-r-negate (ctx value)
  (putnam-1970-b4-unary
   (putnam-1970-b4-negate ctx) value))

(defun putnam-1970-b4-r-subtract (ctx left right)
  (putnam-1970-b4-r-add
   ctx left (putnam-1970-b4-r-negate ctx right)))

(defun putnam-1970-b4-r-multiply (ctx left right)
  (putnam-1970-b4-binary
   (putnam-1970-b4-multiply ctx) left right))

(defun putnam-1970-b4-r-inverse (ctx value)
  (putnam-1970-b4-unary
   (putnam-1970-b4-inverse ctx) value))

(defun putnam-1970-b4-r-divide (ctx numerator denominator)
  (putnam-1970-b4-r-multiply
   ctx numerator
   (putnam-1970-b4-r-inverse ctx denominator)))

(defun putnam-1970-b4-r-less-p (ctx left right)
  (if
      (putnam-1970-b4-binary
       (putnam-1970-b4-less ctx) left right)
      t nil))

(defun putnam-1970-b4-r-less-equal-p (ctx left right)
  (not (putnam-1970-b4-r-less-p ctx right left)))

(defun putnam-1970-b4-r-absolute (ctx value)
  (if
      (putnam-1970-b4-r-less-p
       ctx value (putnam-1970-b4-zero ctx))
      (putnam-1970-b4-r-negate ctx value)
    value))

(defun putnam-1970-b4-positive-p (ctx value)
  (and
   (putnam-1970-b4-member-p
    (putnam-1970-b4-carrier ctx) value)
   (putnam-1970-b4-r-less-p
    ctx (putnam-1970-b4-zero ctx) value)))

(defun putnam-1970-b4-two (ctx)
  (putnam-1970-b4-r-add
   ctx
   (putnam-1970-b4-one ctx)
   (putnam-1970-b4-one ctx)))

(defun putnam-1970-b4-three (ctx)
  (putnam-1970-b4-r-add
   ctx
   (putnam-1970-b4-two ctx)
   (putnam-1970-b4-one ctx)))

(defun putnam-1970-b4-nine (ctx)
  (putnam-1970-b4-r-multiply
   ctx
   (putnam-1970-b4-three ctx)
   (putnam-1970-b4-three ctx)))

(defun putnam-1970-b4-three-halves (ctx)
  (putnam-1970-b4-r-divide
   ctx
   (putnam-1970-b4-three ctx)
   (putnam-1970-b4-two ctx)))

(defun putnam-1970-b4-nine-halves (ctx)
  (putnam-1970-b4-r-divide
   ctx
   (putnam-1970-b4-nine ctx)
   (putnam-1970-b4-two ctx)))

(defun putnam-1970-b4-in-unit-closed-p (ctx value)
  (and
   (putnam-1970-b4-member-p
    (putnam-1970-b4-carrier ctx) value)
   (putnam-1970-b4-r-less-equal-p
    ctx (putnam-1970-b4-zero ctx) value)
   (putnam-1970-b4-r-less-equal-p
    ctx value (putnam-1970-b4-one ctx))))

(defun putnam-1970-b4-in-unit-open-p (ctx value)
  (and
   (putnam-1970-b4-member-p
    (putnam-1970-b4-carrier ctx) value)
   (putnam-1970-b4-r-less-p
    ctx (putnam-1970-b4-zero ctx) value)
   (putnam-1970-b4-r-less-p
    ctx value (putnam-1970-b4-one ctx))))

(defun-sk putnam-1970-b4-real-function-p
    (ctx function)
  (forall (x)
    (implies
     (putnam-1970-b4-member-p
      (putnam-1970-b4-carrier ctx) x)
     (putnam-1970-b4-member-p
      (putnam-1970-b4-carrier ctx)
      (putnam-1970-b4-unary function x)))))

(defun putnam-1970-b4-derivative-error
    (ctx function derivative point y)
  (putnam-1970-b4-r-absolute
   ctx
   (putnam-1970-b4-r-subtract
    ctx
    (putnam-1970-b4-r-subtract
     ctx
     (putnam-1970-b4-unary function y)
     (putnam-1970-b4-unary function point))
    (putnam-1970-b4-r-multiply
     ctx derivative
     (putnam-1970-b4-r-subtract ctx y point)))))

(defun-sk putnam-1970-b4-global-error-bound-p
    (ctx function derivative point epsilon radius)
  (forall (y)
    (implies
     (and
      (putnam-1970-b4-member-p
       (putnam-1970-b4-carrier ctx) y)
      (putnam-1970-b4-r-less-p
       ctx
       (putnam-1970-b4-r-absolute
        ctx (putnam-1970-b4-r-subtract ctx y point))
       radius))
     (putnam-1970-b4-r-less-equal-p
      ctx
      (putnam-1970-b4-derivative-error
       ctx function derivative point y)
      (putnam-1970-b4-r-multiply
       ctx epsilon
       (putnam-1970-b4-r-absolute
        ctx
        (putnam-1970-b4-r-subtract ctx y point)))))))

(defun-sk putnam-1970-b4-global-radius-exists-p
    (ctx function derivative point epsilon)
  (exists (radius)
    (and
     (putnam-1970-b4-positive-p ctx radius)
     (putnam-1970-b4-global-error-bound-p
      ctx function derivative point epsilon radius))))

(defun-sk putnam-1970-b4-has-derivative-at-p
    (ctx function derivative point)
  (forall (epsilon)
    (implies
     (putnam-1970-b4-positive-p ctx epsilon)
     (putnam-1970-b4-global-radius-exists-p
      ctx function derivative point epsilon))))

(defun-sk putnam-1970-b4-differentiable-at-p
    (ctx function point)
  (exists (derivative)
    (and
     (putnam-1970-b4-member-p
      (putnam-1970-b4-carrier ctx) derivative)
     (putnam-1970-b4-has-derivative-at-p
      ctx function derivative point))))

(defun putnam-1970-b4-deriv-value-p
    (ctx function point value)
  (and
   (putnam-1970-b4-member-p
    (putnam-1970-b4-carrier ctx) value)
   (if
       (putnam-1970-b4-has-derivative-at-p
        ctx function (putnam-1970-b4-zero ctx) point)
       (equal value (putnam-1970-b4-zero ctx))
     (if
         (putnam-1970-b4-differentiable-at-p
          ctx function point)
         (putnam-1970-b4-has-derivative-at-p
          ctx function value point)
       (equal value (putnam-1970-b4-zero ctx))))))

(defun-sk putnam-1970-b4-deriv-field-values-p
    (ctx function derivative-field)
  (forall (point)
    (implies
     (putnam-1970-b4-member-p
      (putnam-1970-b4-carrier ctx) point)
     (putnam-1970-b4-deriv-value-p
      ctx function point
      (putnam-1970-b4-unary derivative-field point)))))

(defun putnam-1970-b4-deriv-field-p
    (ctx function derivative-field)
  (and
   (tamep-functionp derivative-field)
   (putnam-1970-b4-real-function-p
    ctx derivative-field)
   (putnam-1970-b4-deriv-field-values-p
    ctx function derivative-field)))

(defun-sk putnam-1970-b4-differentiable-on-unit-p
    (ctx function)
  (forall (point)
    (implies
     (putnam-1970-b4-in-unit-closed-p ctx point)
     (putnam-1970-b4-differentiable-at-p
      ctx function point))))

(defun-sk putnam-1970-b4-speed-bound-p
    (ctx derivative-field)
  (forall (point)
    (implies
     (putnam-1970-b4-in-unit-open-p ctx point)
     (putnam-1970-b4-r-less-equal-p
      ctx
      (putnam-1970-b4-r-absolute
       ctx (putnam-1970-b4-unary derivative-field point))
      (putnam-1970-b4-three-halves ctx)))))

(defun putnam-1970-b4-source-assumptions-p
    (ctx function derivative-field)
  (and
   (putnam-1970-b4-differentiable-on-unit-p
    ctx function)
   (putnam-1970-b4-differentiable-on-unit-p
    ctx derivative-field)
   (equal
    (putnam-1970-b4-r-subtract
     ctx
     (putnam-1970-b4-unary
      function (putnam-1970-b4-one ctx))
     (putnam-1970-b4-unary
      function (putnam-1970-b4-zero ctx)))
    (putnam-1970-b4-one ctx))
   (equal
    (putnam-1970-b4-unary
     derivative-field (putnam-1970-b4-zero ctx))
    (putnam-1970-b4-zero ctx))
   (equal
    (putnam-1970-b4-unary
     derivative-field (putnam-1970-b4-one ctx))
    (putnam-1970-b4-zero ctx))
   (putnam-1970-b4-speed-bound-p
    ctx derivative-field)))

;; This is exactly the negation of the source's existential conclusion.

(defun-sk putnam-1970-b4-no-large-second-derivative-p
    (ctx second-derivative-field)
  (forall (point)
    (implies
     (putnam-1970-b4-in-unit-closed-p ctx point)
     (putnam-1970-b4-r-less-p
      ctx
      (putnam-1970-b4-r-absolute
       ctx
       (putnam-1970-b4-unary
        second-derivative-field point))
      (putnam-1970-b4-nine-halves ctx)))))

(defun-sk putnam-1970-b4-counterexample-p
    (ctx function)
  (exists (derivative-field second-derivative-field)
    (and
     (putnam-1970-b4-deriv-field-p
      ctx function derivative-field)
     (putnam-1970-b4-deriv-field-p
      ctx derivative-field second-derivative-field)
     (putnam-1970-b4-source-assumptions-p
      ctx function derivative-field)
     (putnam-1970-b4-no-large-second-derivative-p
      ctx second-derivative-field))))

(defun putnambench-putnam-1970-b4-statement
    (ctx function)
  (implies
   (and
    (putnam-1970-b4-context-p ctx)
    (tamep-functionp function)
    (putnam-1970-b4-real-function-p ctx function))
   (not
    (putnam-1970-b4-counterexample-p
     ctx function))))

(value-triple :itpeval-statement-checked)
:q
