;; Statement-only formalization of PutnamBench corpus artifact putnam_1966_b6:
;; every twice-differentiable real solution of y''(x) + exp(x)y(x) = 0 is
;; bounded above and below for all sufficiently large x. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar context is a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. Arbitrary subsets and real-valued
;; functions are tame APPLY$ function objects. DEFUN-SK keeps every unbounded
;; universal and existential quantifier internal to the statement.

(defun p66-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p66-unary-value (function x)
  (apply$ function (list x)))

(defun p66-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p66-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p66-member-p carrier x))))

(defun-sk p66-real-function-p (carrier function)
  (forall (x)
    (implies
     (p66-member-p carrier x)
     (p66-member-p
      carrier
      (p66-unary-value function x)))))

(defun-sk p66-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p66-member-p carrier x)
      (p66-member-p carrier y)
      (p66-member-p carrier z))
     (and
      (p66-member-p carrier
                    (p66-binary-value add x y))
      (p66-member-p carrier
                    (p66-binary-value multiply x y))
      (p66-member-p carrier
                    (p66-unary-value negate x))
      (p66-member-p carrier
                    (p66-unary-value inverse x))
      (equal
       (p66-binary-value
        add (p66-binary-value add x y) z)
       (p66-binary-value
        add x (p66-binary-value add y z)))
      (equal (p66-binary-value add x y)
             (p66-binary-value add y x))
      (equal (p66-binary-value add x zero) x)
      (equal
       (p66-binary-value
        add x (p66-unary-value negate x))
       zero)
      (equal
       (p66-binary-value
        multiply (p66-binary-value multiply x y) z)
       (p66-binary-value
        multiply x (p66-binary-value multiply y z)))
      (equal (p66-binary-value multiply x y)
             (p66-binary-value multiply y x))
      (equal (p66-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p66-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p66-binary-value
         multiply x (p66-unary-value inverse x))
        one))
      (equal
       (p66-binary-value
        multiply x (p66-binary-value add y z))
       (p66-binary-value
        add
        (p66-binary-value multiply x y)
        (p66-binary-value multiply x z)))))))

(defun-sk p66-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p66-member-p carrier x)
      (p66-member-p carrier y)
      (p66-member-p carrier z))
     (and
      (not (p66-binary-value less x x))
      (or
       (equal x y)
       (p66-binary-value less x y)
       (p66-binary-value less y x))
      (implies
       (and
        (p66-binary-value less x y)
        (p66-binary-value less y z))
       (p66-binary-value less x z))
      (implies
       (p66-binary-value less x y)
       (p66-binary-value
        less
        (p66-binary-value add x z)
        (p66-binary-value add y z)))
      (implies
       (and
        (p66-binary-value less zero x)
        (p66-binary-value less zero y))
       (p66-binary-value
        less zero (p66-binary-value multiply x y)))))))

(defun-sk p66-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p66-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p66-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p66-member-p carrier x)
      (apply$ set (list x)))
     (not (p66-binary-value less bound x)))))

(defun-sk p66-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p66-member-p carrier bound)
     (p66-upper-bound-p
      carrier less set bound))))

(defun-sk p66-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p66-member-p carrier bound)
      (p66-upper-bound-p carrier less set bound))
     (not (p66-binary-value less bound supremum)))))

(defun p66-supremum-p
    (carrier less set supremum)
  (and
   (p66-member-p carrier supremum)
   (p66-upper-bound-p carrier less set supremum)
   (p66-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p66-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p66-supremum-p
     carrier less set supremum)))

(defun-sk p66-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p66-valid-set-p carrier set)
      (p66-set-nonempty-p carrier set)
      (p66-bounded-above-p carrier less set))
     (p66-has-supremum-p carrier less set))))

(defun p66-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p66-member-p carrier zero)
   (p66-member-p carrier one)
   (not (equal zero one))
   (p66-field-laws-p
    carrier add multiply negate inverse zero one)
   (p66-order-laws-p
    carrier add multiply zero less)
   (p66-binary-value less zero one)
   (p66-dedekind-complete-p carrier less)))

;; The outer context pairs an eight-entry real-field presentation with its
;; exponential function.

(defun p66-field-context (ctx)
  (car ctx))

(defun p66-r-carrier (ctx)
  (nth 0 (p66-field-context ctx)))

(defun p66-r-zero (ctx)
  (nth 1 (p66-field-context ctx)))

(defun p66-r-one (ctx)
  (nth 2 (p66-field-context ctx)))

(defun p66-r-add (ctx)
  (nth 3 (p66-field-context ctx)))

(defun p66-r-mul (ctx)
  (nth 4 (p66-field-context ctx)))

(defun p66-r-neg (ctx)
  (nth 5 (p66-field-context ctx)))

(defun p66-r-inv (ctx)
  (nth 6 (p66-field-context ctx)))

(defun p66-r-lt (ctx)
  (nth 7 (p66-field-context ctx)))

(defun p66-r-exp (ctx)
  (nth 1 ctx))

(defun p66-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p66-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p66-r-add-value (ctx x y)
  (p66-binary-value (p66-r-add ctx) x y))

(defun p66-r-neg-value (ctx x)
  (p66-unary-value (p66-r-neg ctx) x))

(defun p66-r-sub-value (ctx x y)
  (p66-r-add-value
   ctx x (p66-r-neg-value ctx y)))

(defun p66-r-mul-value (ctx x y)
  (p66-binary-value (p66-r-mul ctx) x y))

(defun p66-r-lt-p (ctx x y)
  (if (p66-binary-value (p66-r-lt ctx) x y)
      t nil))

(defun p66-r-le-p (ctx x y)
  (not (p66-r-lt-p ctx y x)))

(defun p66-r-abs-value (ctx x)
  (if (p66-r-lt-p ctx x (p66-r-zero ctx))
      (p66-r-neg-value ctx x)
    x))

(defun p66-positive-real-p (ctx x)
  (and
   (p66-member-p (p66-r-carrier ctx) x)
   (p66-r-lt-p ctx (p66-r-zero ctx) x)))

;; HasDerivAt in epsilon-delta form:
;; |f(z)-f(x)-d(z-x)| <= epsilon |z-x| near x.

(defun-sk p66-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (z)
    (implies
     (and
      (p66-member-p (p66-r-carrier ctx) z)
      (p66-r-lt-p
       ctx
       (p66-r-abs-value
        ctx (p66-r-sub-value ctx z x))
       radius))
     (p66-r-le-p
      ctx
      (p66-r-abs-value
       ctx
       (p66-r-sub-value
        ctx
        (p66-r-sub-value
         ctx
         (p66-unary-value function z)
         (p66-unary-value function x))
        (p66-r-mul-value
         ctx derivative
         (p66-r-sub-value ctx z x))))
      (p66-r-mul-value
       ctx epsilon
       (p66-r-abs-value
        ctx (p66-r-sub-value ctx z x)))))))

(defun-sk p66-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p66-positive-real-p ctx radius)
     (p66-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p66-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p66-positive-real-p ctx epsilon)
     (p66-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p66-global-derivative-values-p
    (ctx function derivative-function)
  (forall (x)
    (implies
     (p66-member-p (p66-r-carrier ctx) x)
     (p66-has-derivative-at-p
      ctx
      function
      (p66-unary-value derivative-function x)
      x))))

(defun p66-global-derivative-function-p
    (ctx function derivative-function)
  (and
   (tamep-functionp function)
   (tamep-functionp derivative-function)
   (p66-real-function-p
    (p66-r-carrier ctx) function)
   (p66-real-function-p
    (p66-r-carrier ctx) derivative-function)
   (p66-global-derivative-values-p
    ctx function derivative-function)))

(defun-sk p66-differentiable-p (ctx function)
  (exists (derivative-function)
    (p66-global-derivative-function-p
     ctx function derivative-function)))

;; A derivative is unique on a real field. DEFCHOOSE conservatively selects
;; that unique function while leaving the existential differentiability
;; assumptions inside the statement.

(defchoose p66-derivative-function
    (derivative-function)
    (ctx function)
  (p66-global-derivative-function-p
   ctx function derivative-function))

;; The real exponential is characterized without extra analytic axioms as the
;; unique globally differentiable function E satisfying E' = E and E(0) = 1.

(defun p66-exponential-function-p (ctx exponential)
  (and
   (p66-global-derivative-function-p
    ctx exponential exponential)
   (equal
    (p66-unary-value exponential (p66-r-zero ctx))
    (p66-r-one ctx))))

(defun p66-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 2)
   (p66-field-context-p (p66-field-context ctx))
   (tamep-functionp (p66-r-exp ctx))
   (p66-exponential-function-p
    ctx (p66-r-exp ctx))))

;; The source differential equation, using the internally selected first and
;; second derivative functions.

(defun p66-first-derivative (ctx function)
  (p66-derivative-function ctx function))

(defun p66-second-derivative (ctx function)
  (p66-derivative-function
   ctx (p66-first-derivative ctx function)))

(defun-sk p66-differential-equation-p (ctx function)
  (forall (x)
    (implies
     (p66-member-p (p66-r-carrier ctx) x)
     (equal
      (p66-r-add-value
       ctx
       (p66-unary-value
        (p66-second-derivative ctx function) x)
       (p66-r-mul-value
        ctx
        (p66-unary-value (p66-r-exp ctx) x)
        (p66-unary-value function x)))
      (p66-r-zero ctx)))))

(defun-sk p66-tail-bounded-p
    (ctx function lower upper cutoff)
  (forall (x)
    (implies
     (and
      (p66-member-p (p66-r-carrier ctx) x)
      (p66-r-lt-p ctx cutoff x))
     (and
      (p66-r-le-p
       ctx lower (p66-unary-value function x))
      (p66-r-le-p
       ctx (p66-unary-value function x) upper)))))

(defun-sk p66-eventually-bounded-p (ctx function)
  (exists (lower upper cutoff)
    (and
     (p66-member-p (p66-r-carrier ctx) lower)
     (p66-member-p (p66-r-carrier ctx) upper)
     (p66-member-p (p66-r-carrier ctx) cutoff)
     (p66-tail-bounded-p
      ctx function lower upper cutoff))))

(defun putnambench-putnam-1966-b6-statement (ctx y)
  (implies
   (and
    (p66-context-p ctx)
    (tamep-functionp y)
    (p66-real-function-p (p66-r-carrier ctx) y)
    (p66-differentiable-p ctx y)
    (p66-differentiable-p
     ctx (p66-first-derivative ctx y))
    (p66-differential-equation-p ctx y))
   (p66-eventually-bounded-p ctx y)))

(value-triple :itpeval-statement-checked)
:q
