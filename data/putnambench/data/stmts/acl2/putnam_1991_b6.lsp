;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_b6:
;; for positive real a and b, |log(a/b)| is the greatest cutoff for the
;; stated hyperbolic-sine interpolation inequality. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism, together with its exponential and
;; logarithm. Arbitrary subsets and functions are tame APPLY$ function
;; objects. The exponential is characterized by exp(0)=1 and exp'=exp, and
;; logarithm is its inverse on the positive reals. Thus real powers and sinh
;; below are definitions of the source operations, not rational or finite
;; approximations.

(defun p91b6-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p91b6-unary-value (function x)
  (apply$ function (list x)))

(defun p91b6-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p91b6-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p91b6-member-p carrier x))))

(defun-sk p91b6-real-function-p (carrier function)
  (forall (x)
    (implies
     (p91b6-member-p carrier x)
     (p91b6-member-p
      carrier
      (p91b6-unary-value function x)))))

(defun-sk p91b6-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p91b6-member-p carrier x)
      (p91b6-member-p carrier y)
      (p91b6-member-p carrier z))
     (and
      (p91b6-member-p
       carrier (p91b6-binary-value add x y))
      (p91b6-member-p
       carrier (p91b6-binary-value multiply x y))
      (p91b6-member-p
       carrier (p91b6-unary-value negate x))
      (p91b6-member-p
       carrier (p91b6-unary-value inverse x))
      (equal
       (p91b6-binary-value
        add (p91b6-binary-value add x y) z)
       (p91b6-binary-value
        add x (p91b6-binary-value add y z)))
      (equal
       (p91b6-binary-value add x y)
       (p91b6-binary-value add y x))
      (equal (p91b6-binary-value add x zero) x)
      (equal
       (p91b6-binary-value
        add x (p91b6-unary-value negate x))
       zero)
      (equal
       (p91b6-binary-value
        multiply (p91b6-binary-value multiply x y) z)
       (p91b6-binary-value
        multiply x (p91b6-binary-value multiply y z)))
      (equal
       (p91b6-binary-value multiply x y)
       (p91b6-binary-value multiply y x))
      (equal
       (p91b6-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p91b6-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p91b6-binary-value
         multiply x (p91b6-unary-value inverse x))
        one))
      (equal
       (p91b6-binary-value
        multiply x (p91b6-binary-value add y z))
       (p91b6-binary-value
        add
        (p91b6-binary-value multiply x y)
        (p91b6-binary-value multiply x z)))))))

(defun-sk p91b6-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p91b6-member-p carrier x)
      (p91b6-member-p carrier y)
      (p91b6-member-p carrier z))
     (and
      (not (p91b6-binary-value less x x))
      (or
       (equal x y)
       (p91b6-binary-value less x y)
       (p91b6-binary-value less y x))
      (implies
       (and
        (p91b6-binary-value less x y)
        (p91b6-binary-value less y z))
       (p91b6-binary-value less x z))
      (implies
       (p91b6-binary-value less x y)
       (p91b6-binary-value
        less
        (p91b6-binary-value add x z)
        (p91b6-binary-value add y z)))
      (implies
       (and
        (p91b6-binary-value less zero x)
        (p91b6-binary-value less zero y))
       (p91b6-binary-value
        less zero
        (p91b6-binary-value multiply x y)))))))

(defun-sk p91b6-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p91b6-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p91b6-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p91b6-member-p carrier x)
      (apply$ set (list x)))
     (not (p91b6-binary-value less bound x)))))

(defun-sk p91b6-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p91b6-member-p carrier bound)
     (p91b6-upper-bound-p
      carrier less set bound))))

(defun-sk p91b6-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p91b6-member-p carrier bound)
      (p91b6-upper-bound-p carrier less set bound))
     (not (p91b6-binary-value less bound supremum)))))

(defun p91b6-supremum-p
    (carrier less set supremum)
  (and
   (p91b6-member-p carrier supremum)
   (p91b6-upper-bound-p carrier less set supremum)
   (p91b6-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p91b6-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p91b6-supremum-p
     carrier less set supremum)))

(defun-sk p91b6-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p91b6-valid-set-p carrier set)
      (p91b6-set-nonempty-p carrier set)
      (p91b6-bounded-above-p carrier less set))
     (p91b6-has-supremum-p carrier less set))))

(defun p91b6-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p91b6-member-p carrier zero)
   (p91b6-member-p carrier one)
   (not (equal zero one))
   (p91b6-field-laws-p
    carrier add multiply negate inverse zero one)
   (p91b6-order-laws-p
    carrier add multiply zero less)
   (p91b6-binary-value less zero one)
   (p91b6-dedekind-complete-p carrier less)))

;; The outer context is (field-context exponential logarithm), where the
;; field context is (carrier zero one add multiply negate inverse less).

(defun p91b6-field-context (ctx)
  (nth 0 ctx))

(defun p91b6-r-carrier (ctx)
  (nth 0 (p91b6-field-context ctx)))

(defun p91b6-r-zero (ctx)
  (nth 1 (p91b6-field-context ctx)))

(defun p91b6-r-one (ctx)
  (nth 2 (p91b6-field-context ctx)))

(defun p91b6-r-add (ctx)
  (nth 3 (p91b6-field-context ctx)))

(defun p91b6-r-mul (ctx)
  (nth 4 (p91b6-field-context ctx)))

(defun p91b6-r-neg (ctx)
  (nth 5 (p91b6-field-context ctx)))

(defun p91b6-r-inv (ctx)
  (nth 6 (p91b6-field-context ctx)))

(defun p91b6-r-lt (ctx)
  (nth 7 (p91b6-field-context ctx)))

(defun p91b6-r-exp (ctx)
  (nth 1 ctx))

(defun p91b6-r-log (ctx)
  (nth 2 ctx))

(defun p91b6-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p91b6-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p91b6-r-add-value (ctx x y)
  (p91b6-binary-value (p91b6-r-add ctx) x y))

(defun p91b6-r-neg-value (ctx x)
  (p91b6-unary-value (p91b6-r-neg ctx) x))

(defun p91b6-r-sub-value (ctx x y)
  (p91b6-r-add-value
   ctx x (p91b6-r-neg-value ctx y)))

(defun p91b6-r-mul-value (ctx x y)
  (p91b6-binary-value (p91b6-r-mul ctx) x y))

(defun p91b6-r-inv-value (ctx x)
  (p91b6-unary-value (p91b6-r-inv ctx) x))

(defun p91b6-r-div-value (ctx x y)
  (p91b6-r-mul-value
   ctx x (p91b6-r-inv-value ctx y)))

(defun p91b6-r-lt-p (ctx x y)
  (if (p91b6-binary-value (p91b6-r-lt ctx) x y)
      t nil))

(defun p91b6-r-le-p (ctx x y)
  (not (p91b6-r-lt-p ctx y x)))

(defun p91b6-r-abs-value (ctx x)
  (if (p91b6-r-lt-p ctx x (p91b6-r-zero ctx))
      (p91b6-r-neg-value ctx x)
    x))

(defun p91b6-positive-real-p (ctx x)
  (and
   (p91b6-member-p (p91b6-r-carrier ctx) x)
   (p91b6-r-lt-p ctx (p91b6-r-zero ctx) x)))

(defun p91b6-r-two (ctx)
  (p91b6-r-add-value
   ctx (p91b6-r-one ctx) (p91b6-r-one ctx)))

;; HasDerivAt in epsilon-delta form:
;; |f(z)-f(x)-d(z-x)| <= epsilon*|z-x| near x.

(defun-sk p91b6-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (z)
    (implies
     (and
      (p91b6-member-p (p91b6-r-carrier ctx) z)
      (p91b6-r-lt-p
       ctx
       (p91b6-r-abs-value
        ctx (p91b6-r-sub-value ctx z x))
       radius))
     (p91b6-r-le-p
      ctx
      (p91b6-r-abs-value
       ctx
       (p91b6-r-sub-value
        ctx
        (p91b6-r-sub-value
         ctx
         (p91b6-unary-value function z)
         (p91b6-unary-value function x))
        (p91b6-r-mul-value
         ctx derivative
         (p91b6-r-sub-value ctx z x))))
      (p91b6-r-mul-value
       ctx epsilon
       (p91b6-r-abs-value
        ctx (p91b6-r-sub-value ctx z x)))))))

(defun-sk p91b6-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p91b6-positive-real-p ctx radius)
     (p91b6-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p91b6-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p91b6-positive-real-p ctx epsilon)
     (p91b6-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p91b6-exponential-derivative-values-p (ctx)
  (forall (x)
    (implies
     (p91b6-member-p (p91b6-r-carrier ctx) x)
     (p91b6-has-derivative-at-p
      ctx
      (p91b6-r-exp ctx)
      (p91b6-unary-value (p91b6-r-exp ctx) x)
      x))))

(defun-sk p91b6-exponential-positive-p (ctx)
  (forall (x)
    (implies
     (p91b6-member-p (p91b6-r-carrier ctx) x)
     (p91b6-positive-real-p
      ctx
      (p91b6-unary-value (p91b6-r-exp ctx) x)))))

(defun p91b6-exponential-function-p (ctx)
  (and
   (tamep-functionp (p91b6-r-exp ctx))
   (p91b6-real-function-p
    (p91b6-r-carrier ctx) (p91b6-r-exp ctx))
   (equal
    (p91b6-unary-value
     (p91b6-r-exp ctx) (p91b6-r-zero ctx))
    (p91b6-r-one ctx))
   (p91b6-exponential-derivative-values-p ctx)
   (p91b6-exponential-positive-p ctx)))

(defun-sk p91b6-log-exp-inverse-p (ctx)
  (forall (x)
    (implies
     (p91b6-member-p (p91b6-r-carrier ctx) x)
     (equal
      (p91b6-unary-value
       (p91b6-r-log ctx)
       (p91b6-unary-value (p91b6-r-exp ctx) x))
      x))))

(defun-sk p91b6-exp-log-inverse-p (ctx)
  (forall (x)
    (implies
     (p91b6-positive-real-p ctx x)
     (equal
      (p91b6-unary-value
       (p91b6-r-exp ctx)
       (p91b6-unary-value (p91b6-r-log ctx) x))
      x))))

(defun p91b6-logarithm-function-p (ctx)
  (and
   (tamep-functionp (p91b6-r-log ctx))
   (p91b6-real-function-p
    (p91b6-r-carrier ctx) (p91b6-r-log ctx))
   (p91b6-log-exp-inverse-p ctx)
   (p91b6-exp-log-inverse-p ctx)))

(defun p91b6-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 3)
   (p91b6-field-context-p (p91b6-field-context ctx))
   (p91b6-exponential-function-p ctx)
   (p91b6-logarithm-function-p ctx)))

;; Source operations.

(defun p91b6-exp-value (ctx x)
  (p91b6-unary-value (p91b6-r-exp ctx) x))

(defun p91b6-log-value (ctx x)
  (p91b6-unary-value (p91b6-r-log ctx) x))

(defun p91b6-real-power-value (ctx base exponent)
  (p91b6-exp-value
   ctx
   (p91b6-r-mul-value
    ctx exponent (p91b6-log-value ctx base))))

(defun p91b6-sinh-value (ctx x)
  (p91b6-r-div-value
   ctx
   (p91b6-r-sub-value
    ctx
    (p91b6-exp-value ctx x)
    (p91b6-exp-value
     ctx (p91b6-r-neg-value ctx x)))
   (p91b6-r-two ctx)))

(defun p91b6-solution-value (ctx a b)
  (p91b6-r-abs-value
   ctx
   (p91b6-log-value
    ctx
    (p91b6-r-div-value ctx a b))))

(defun p91b6-left-side (ctx a b x)
  (p91b6-r-mul-value
   ctx
   (p91b6-real-power-value ctx a x)
   (p91b6-real-power-value
    ctx b
    (p91b6-r-sub-value
     ctx (p91b6-r-one ctx) x))))

(defun p91b6-right-side (ctx a b u x)
  (p91b6-r-add-value
   ctx
   (p91b6-r-mul-value
    ctx
    a
    (p91b6-r-div-value
     ctx
     (p91b6-sinh-value
      ctx (p91b6-r-mul-value ctx u x))
     (p91b6-sinh-value ctx u)))
   (p91b6-r-mul-value
    ctx
    b
    (p91b6-r-div-value
     ctx
     (p91b6-sinh-value
      ctx
      (p91b6-r-mul-value
       ctx u
       (p91b6-r-sub-value
        ctx (p91b6-r-one ctx) x)))
     (p91b6-sinh-value ctx u)))))

(defun-sk p91b6-inequality-for-all-x-p
    (ctx a b u)
  (forall (x)
    (implies
     (and
      (p91b6-member-p (p91b6-r-carrier ctx) x)
      (p91b6-r-lt-p ctx (p91b6-r-zero ctx) x)
      (p91b6-r-lt-p ctx x (p91b6-r-one ctx)))
     (p91b6-r-le-p
      ctx
      (p91b6-left-side ctx a b x)
      (p91b6-right-side ctx a b u x)))))

(defun-sk p91b6-cutoff-admissible-p
    (ctx a b cutoff)
  (forall (u)
    (implies
     (and
      (p91b6-member-p (p91b6-r-carrier ctx) u)
      (p91b6-r-lt-p
       ctx
       (p91b6-r-zero ctx)
       (p91b6-r-abs-value ctx u))
      (p91b6-r-le-p
       ctx
       (p91b6-r-abs-value ctx u)
       cutoff))
     (p91b6-inequality-for-all-x-p
      ctx a b u))))

(defun-sk p91b6-every-admissible-cutoff-at-most-p
    (ctx a b greatest)
  (forall (cutoff)
    (implies
     (and
      (p91b6-member-p
       (p91b6-r-carrier ctx) cutoff)
      (p91b6-cutoff-admissible-p
       ctx a b cutoff))
     (p91b6-r-le-p ctx cutoff greatest))))

(defun p91b6-greatest-cutoff-p
    (ctx a b greatest)
  (and
   (p91b6-member-p
    (p91b6-r-carrier ctx) greatest)
   (p91b6-cutoff-admissible-p
    ctx a b greatest)
   (p91b6-every-admissible-cutoff-at-most-p
    ctx a b greatest)))

(defun-sk putnambench-putnam-1991-b6-statement (ctx)
  (forall (a b)
    (implies
     (and
      (p91b6-context-p ctx)
      (p91b6-positive-real-p ctx a)
      (p91b6-positive-real-p ctx b))
     (p91b6-greatest-cutoff-p
      ctx a b
      (p91b6-solution-value ctx a b)))))

(value-triple :itpeval-statement-checked)
:q
