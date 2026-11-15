;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_b3:
;; positive differentiable real functions satisfying a derivative functional
;; equation are exactly a constrained family of positive power functions.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism, together with its standard
;; exponential and logarithm. Tame APPLY$ objects retain the arbitrary
;; real-valued function. DEFUN-SK keeps all unbounded mathematical
;; quantifiers internal. Derivatives use the epsilon-delta definition, and
;; positive-base real powers are definitionally exp(d * log(x)).

(defun p05b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p05b3-unary-value (function x)
  (apply$ function (list x)))

(defun p05b3-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p05b3-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p05b3-member-p carrier x))))

(defun-sk p05b3-real-function-p (carrier function)
  (forall (x)
    (implies
     (p05b3-member-p carrier x)
     (p05b3-member-p
      carrier
      (p05b3-unary-value function x)))))

(defun-sk p05b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p05b3-member-p carrier x)
      (p05b3-member-p carrier y)
      (p05b3-member-p carrier z))
     (and
      (p05b3-member-p carrier
                      (p05b3-binary-value add x y))
      (p05b3-member-p carrier
                      (p05b3-binary-value multiply x y))
      (p05b3-member-p carrier
                      (p05b3-unary-value negate x))
      (p05b3-member-p carrier
                      (p05b3-unary-value inverse x))
      (equal
       (p05b3-binary-value
        add (p05b3-binary-value add x y) z)
       (p05b3-binary-value
        add x (p05b3-binary-value add y z)))
      (equal
       (p05b3-binary-value add x y)
       (p05b3-binary-value add y x))
      (equal (p05b3-binary-value add x zero) x)
      (equal
       (p05b3-binary-value
        add x (p05b3-unary-value negate x))
       zero)
      (equal
       (p05b3-binary-value
        multiply (p05b3-binary-value multiply x y) z)
       (p05b3-binary-value
        multiply x (p05b3-binary-value multiply y z)))
      (equal
       (p05b3-binary-value multiply x y)
       (p05b3-binary-value multiply y x))
      (equal (p05b3-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p05b3-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p05b3-binary-value
         multiply x (p05b3-unary-value inverse x))
        one))
      (equal
       (p05b3-binary-value
        multiply x (p05b3-binary-value add y z))
       (p05b3-binary-value
        add
        (p05b3-binary-value multiply x y)
        (p05b3-binary-value multiply x z)))))))

(defun-sk p05b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p05b3-member-p carrier x)
      (p05b3-member-p carrier y)
      (p05b3-member-p carrier z))
     (and
      (not (p05b3-binary-value less x x))
      (or
       (equal x y)
       (p05b3-binary-value less x y)
       (p05b3-binary-value less y x))
      (implies
       (and
        (p05b3-binary-value less x y)
        (p05b3-binary-value less y z))
       (p05b3-binary-value less x z))
      (implies
       (p05b3-binary-value less x y)
       (p05b3-binary-value
        less
        (p05b3-binary-value add x z)
        (p05b3-binary-value add y z)))
      (implies
       (and
        (p05b3-binary-value less zero x)
        (p05b3-binary-value less zero y))
       (p05b3-binary-value
        less zero (p05b3-binary-value multiply x y)))))))

(defun-sk p05b3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p05b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p05b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p05b3-member-p carrier x)
      (apply$ set (list x)))
     (not (p05b3-binary-value less bound x)))))

(defun-sk p05b3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p05b3-member-p carrier bound)
     (p05b3-upper-bound-p
      carrier less set bound))))

(defun-sk p05b3-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p05b3-member-p carrier bound)
      (p05b3-upper-bound-p carrier less set bound))
     (not (p05b3-binary-value less bound supremum)))))

(defun p05b3-supremum-p
    (carrier less set supremum)
  (and
   (p05b3-member-p carrier supremum)
   (p05b3-upper-bound-p carrier less set supremum)
   (p05b3-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p05b3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p05b3-supremum-p
     carrier less set supremum)))

(defun-sk p05b3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p05b3-valid-set-p carrier set)
      (p05b3-set-nonempty-p carrier set)
      (p05b3-bounded-above-p carrier less set))
     (p05b3-has-supremum-p carrier less set))))

(defun p05b3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p05b3-member-p carrier zero)
   (p05b3-member-p carrier one)
   (not (equal zero one))
   (p05b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p05b3-order-laws-p
    carrier add multiply zero less)
   (p05b3-binary-value less zero one)
   (p05b3-dedekind-complete-p carrier less)))

;; The outer context is (field-context exponential logarithm).

(defun p05b3-field-context (ctx)
  (nth 0 ctx))

(defun p05b3-r-carrier (ctx)
  (nth 0 (p05b3-field-context ctx)))

(defun p05b3-r-zero (ctx)
  (nth 1 (p05b3-field-context ctx)))

(defun p05b3-r-one (ctx)
  (nth 2 (p05b3-field-context ctx)))

(defun p05b3-r-add (ctx)
  (nth 3 (p05b3-field-context ctx)))

(defun p05b3-r-mul (ctx)
  (nth 4 (p05b3-field-context ctx)))

(defun p05b3-r-neg (ctx)
  (nth 5 (p05b3-field-context ctx)))

(defun p05b3-r-inv (ctx)
  (nth 6 (p05b3-field-context ctx)))

(defun p05b3-r-lt (ctx)
  (nth 7 (p05b3-field-context ctx)))

(defun p05b3-r-exp (ctx)
  (nth 1 ctx))

(defun p05b3-r-log (ctx)
  (nth 2 ctx))

(defun p05b3-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p05b3-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p05b3-r-add-value (ctx x y)
  (p05b3-binary-value (p05b3-r-add ctx) x y))

(defun p05b3-r-neg-value (ctx x)
  (p05b3-unary-value (p05b3-r-neg ctx) x))

(defun p05b3-r-sub-value (ctx x y)
  (p05b3-r-add-value
   ctx x (p05b3-r-neg-value ctx y)))

(defun p05b3-r-mul-value (ctx x y)
  (p05b3-binary-value (p05b3-r-mul ctx) x y))

(defun p05b3-r-inv-value (ctx x)
  (p05b3-unary-value (p05b3-r-inv ctx) x))

(defun p05b3-r-div-value (ctx numerator denominator)
  (p05b3-r-mul-value
   ctx numerator (p05b3-r-inv-value ctx denominator)))

(defun p05b3-r-lt-p (ctx x y)
  (if (p05b3-binary-value (p05b3-r-lt ctx) x y)
      t nil))

(defun p05b3-r-le-p (ctx x y)
  (not (p05b3-r-lt-p ctx y x)))

(defun p05b3-r-abs-value (ctx x)
  (if (p05b3-r-lt-p ctx x (p05b3-r-zero ctx))
      (p05b3-r-neg-value ctx x)
    x))

(defun p05b3-positive-real-p (ctx x)
  (and
   (p05b3-member-p (p05b3-r-carrier ctx) x)
   (p05b3-r-lt-p ctx (p05b3-r-zero ctx) x)))

;; HasDerivAt in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun-sk p05b3-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p05b3-member-p (p05b3-r-carrier ctx) y)
      (p05b3-r-lt-p
       ctx
       (p05b3-r-abs-value
        ctx (p05b3-r-sub-value ctx y x))
       radius))
     (p05b3-r-le-p
      ctx
      (p05b3-r-abs-value
       ctx
       (p05b3-r-sub-value
        ctx
        (p05b3-r-sub-value
         ctx
         (p05b3-unary-value function y)
         (p05b3-unary-value function x))
        (p05b3-r-mul-value
         ctx derivative
         (p05b3-r-sub-value ctx y x))))
      (p05b3-r-mul-value
       ctx epsilon
       (p05b3-r-abs-value
        ctx (p05b3-r-sub-value ctx y x)))))))

(defun-sk p05b3-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p05b3-positive-real-p ctx radius)
     (p05b3-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p05b3-derivative-epsilon-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p05b3-positive-real-p ctx epsilon)
     (p05b3-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun p05b3-has-derivative-at-p
    (ctx function derivative x)
  (and
   (p05b3-member-p (p05b3-r-carrier ctx) derivative)
   (p05b3-member-p (p05b3-r-carrier ctx) x)
   (p05b3-derivative-epsilon-p
    ctx function derivative x)))

(defun-sk p05b3-derivative-exists-at-p
    (ctx function x)
  (exists (derivative)
    (p05b3-has-derivative-at-p
     ctx function derivative x)))

(defun-sk p05b3-differentiable-on-positive-p
    (ctx function)
  (forall (x)
    (implies
     (p05b3-positive-real-p ctx x)
     (p05b3-derivative-exists-at-p
      ctx function x))))

;; The differential initial-value problem E' = E, E(0) = 1 characterizes the
;; standard real exponential. LOG is its inverse on the positive reals.

(defun-sk p05b3-exponential-laws-p (ctx)
  (forall (x)
    (implies
     (p05b3-member-p (p05b3-r-carrier ctx) x)
     (and
      (p05b3-positive-real-p
       ctx (p05b3-unary-value (p05b3-r-exp ctx) x))
      (p05b3-has-derivative-at-p
       ctx
       (p05b3-r-exp ctx)
       (p05b3-unary-value (p05b3-r-exp ctx) x)
       x)))))

(defun p05b3-exponential-function-p (ctx)
  (and
   (tamep-functionp (p05b3-r-exp ctx))
   (p05b3-real-function-p
    (p05b3-r-carrier ctx) (p05b3-r-exp ctx))
   (equal
    (p05b3-unary-value
     (p05b3-r-exp ctx) (p05b3-r-zero ctx))
    (p05b3-r-one ctx))
   (p05b3-exponential-laws-p ctx)))

(defun-sk p05b3-logarithm-laws-p (ctx)
  (forall (x)
    (implies
     (p05b3-member-p (p05b3-r-carrier ctx) x)
     (and
      (equal
       (p05b3-unary-value
        (p05b3-r-log ctx)
        (p05b3-unary-value (p05b3-r-exp ctx) x))
       x)
      (implies
       (p05b3-positive-real-p ctx x)
       (equal
        (p05b3-unary-value
         (p05b3-r-exp ctx)
         (p05b3-unary-value (p05b3-r-log ctx) x))
        x))))))

(defun p05b3-logarithm-function-p (ctx)
  (and
   (tamep-functionp (p05b3-r-log ctx))
   (p05b3-real-function-p
    (p05b3-r-carrier ctx) (p05b3-r-log ctx))
   (p05b3-logarithm-laws-p ctx)))

(defun p05b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 3)
   (p05b3-field-context-p (p05b3-field-context ctx))
   (p05b3-exponential-function-p ctx)
   (p05b3-logarithm-function-p ctx)))

(defun p05b3-real-power-value (ctx base exponent)
  (p05b3-unary-value
   (p05b3-r-exp ctx)
   (p05b3-r-mul-value
    ctx exponent
    (p05b3-unary-value (p05b3-r-log ctx) base))))

(defun-sk p05b3-positive-values-p (ctx function)
  (forall (x)
    (implies
     (p05b3-positive-real-p ctx x)
     (p05b3-positive-real-p
      ctx (p05b3-unary-value function x)))))

;; The equation uses HasDerivAt at a/x with derivative x/f(x). Under the
;; differentiability hypothesis, uniqueness of real derivatives makes this
;; bidirectionally equivalent to deriv(f, a/x) = x/f(x).

(defun-sk p05b3-functional-equation-at-p
    (ctx function a)
  (forall (x)
    (implies
     (p05b3-positive-real-p ctx x)
     (p05b3-has-derivative-at-p
      ctx
      function
      (p05b3-r-div-value
       ctx x (p05b3-unary-value function x))
      (p05b3-r-div-value ctx a x)))))

(defun-sk p05b3-functional-equation-exists-p
    (ctx function)
  (exists (a)
    (and
     (p05b3-positive-real-p ctx a)
     (p05b3-functional-equation-at-p
      ctx function a))))

(defun-sk p05b3-power-family-at-p
    (ctx function c d)
  (forall (x)
    (implies
     (p05b3-positive-real-p ctx x)
     (equal
      (p05b3-unary-value function x)
      (p05b3-r-mul-value
       ctx c (p05b3-real-power-value ctx x d))))))

(defun-sk p05b3-solution-p (ctx function)
  (exists (c d)
    (and
     (p05b3-positive-real-p ctx c)
     (p05b3-positive-real-p ctx d)
     (implies
      (equal d (p05b3-r-one ctx))
      (equal c (p05b3-r-one ctx)))
     (p05b3-power-family-at-p
      ctx function c d))))

(defun putnambench-putnam-2005-b3-statement
    (ctx function)
  (implies
   (and
    (p05b3-context-p ctx)
    (tamep-functionp function)
    (p05b3-real-function-p
     (p05b3-r-carrier ctx) function)
    (p05b3-positive-values-p ctx function)
    (p05b3-differentiable-on-positive-p
     ctx function))
   (equal
    (p05b3-functional-equation-exists-p
     ctx function)
    (p05b3-solution-p ctx function))))

(value-triple :itpeval-statement-checked)
:q
