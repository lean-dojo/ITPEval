;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_b3:
;; the real exponents k for which every positive differentiable function with
;; f'(x) > f(x) eventually dominates exp(k*x) are exactly those with k < 1.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism, together with its exponential.
;; Arbitrary subsets and real-valued functions are tame APPLY$ function
;; objects. DEFUN-SK keeps every unbounded mathematical quantifier and
;; analytic witness internal to the statement. Derivatives use their usual
;; epsilon-delta definition, and exp is characterized by exp(0) = 1 and
;; exp' = exp.

(defun p94b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p94b3-unary-value (function x)
  (apply$ function (list x)))

(defun p94b3-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p94b3-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p94b3-member-p carrier x))))

(defun-sk p94b3-real-function-p (carrier function)
  (forall (x)
    (implies
     (p94b3-member-p carrier x)
     (p94b3-member-p
      carrier
      (p94b3-unary-value function x)))))

(defun-sk p94b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p94b3-member-p carrier x)
      (p94b3-member-p carrier y)
      (p94b3-member-p carrier z))
     (and
      (p94b3-member-p carrier
                    (p94b3-binary-value add x y))
      (p94b3-member-p carrier
                    (p94b3-binary-value multiply x y))
      (p94b3-member-p carrier
                    (p94b3-unary-value negate x))
      (p94b3-member-p carrier
                    (p94b3-unary-value inverse x))
      (equal
       (p94b3-binary-value
        add (p94b3-binary-value add x y) z)
       (p94b3-binary-value
        add x (p94b3-binary-value add y z)))
      (equal (p94b3-binary-value add x y)
             (p94b3-binary-value add y x))
      (equal (p94b3-binary-value add x zero) x)
      (equal
       (p94b3-binary-value
        add x (p94b3-unary-value negate x))
       zero)
      (equal
       (p94b3-binary-value
        multiply (p94b3-binary-value multiply x y) z)
       (p94b3-binary-value
        multiply x (p94b3-binary-value multiply y z)))
      (equal (p94b3-binary-value multiply x y)
             (p94b3-binary-value multiply y x))
      (equal (p94b3-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p94b3-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p94b3-binary-value
         multiply x (p94b3-unary-value inverse x))
        one))
      (equal
       (p94b3-binary-value
        multiply x (p94b3-binary-value add y z))
       (p94b3-binary-value
        add
        (p94b3-binary-value multiply x y)
        (p94b3-binary-value multiply x z)))))))

(defun-sk p94b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p94b3-member-p carrier x)
      (p94b3-member-p carrier y)
      (p94b3-member-p carrier z))
     (and
      (not (p94b3-binary-value less x x))
      (or
       (equal x y)
       (p94b3-binary-value less x y)
       (p94b3-binary-value less y x))
      (implies
       (and
        (p94b3-binary-value less x y)
        (p94b3-binary-value less y z))
       (p94b3-binary-value less x z))
      (implies
       (p94b3-binary-value less x y)
       (p94b3-binary-value
        less
        (p94b3-binary-value add x z)
        (p94b3-binary-value add y z)))
      (implies
       (and
        (p94b3-binary-value less zero x)
        (p94b3-binary-value less zero y))
       (p94b3-binary-value
        less zero (p94b3-binary-value multiply x y)))))))

(defun-sk p94b3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p94b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p94b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p94b3-member-p carrier x)
      (apply$ set (list x)))
     (not (p94b3-binary-value less bound x)))))

(defun-sk p94b3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p94b3-member-p carrier bound)
     (p94b3-upper-bound-p
      carrier less set bound))))

(defun-sk p94b3-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p94b3-member-p carrier bound)
      (p94b3-upper-bound-p carrier less set bound))
     (not (p94b3-binary-value less bound supremum)))))

(defun p94b3-supremum-p
    (carrier less set supremum)
  (and
   (p94b3-member-p carrier supremum)
   (p94b3-upper-bound-p carrier less set supremum)
   (p94b3-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p94b3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p94b3-supremum-p
     carrier less set supremum)))

(defun-sk p94b3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p94b3-valid-set-p carrier set)
      (p94b3-set-nonempty-p carrier set)
      (p94b3-bounded-above-p carrier less set))
     (p94b3-has-supremum-p carrier less set))))

(defun p94b3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p94b3-member-p carrier zero)
   (p94b3-member-p carrier one)
   (not (equal zero one))
   (p94b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p94b3-order-laws-p
    carrier add multiply zero less)
   (p94b3-binary-value less zero one)
   (p94b3-dedekind-complete-p carrier less)))

;; The outer context is (field-context exponential).

(defun p94b3-field-context (ctx)
  (nth 0 ctx))

(defun p94b3-r-carrier (ctx)
  (nth 0 (p94b3-field-context ctx)))

(defun p94b3-r-zero (ctx)
  (nth 1 (p94b3-field-context ctx)))

(defun p94b3-r-one (ctx)
  (nth 2 (p94b3-field-context ctx)))

(defun p94b3-r-add (ctx)
  (nth 3 (p94b3-field-context ctx)))

(defun p94b3-r-mul (ctx)
  (nth 4 (p94b3-field-context ctx)))

(defun p94b3-r-neg (ctx)
  (nth 5 (p94b3-field-context ctx)))

(defun p94b3-r-inv (ctx)
  (nth 6 (p94b3-field-context ctx)))

(defun p94b3-r-lt (ctx)
  (nth 7 (p94b3-field-context ctx)))

(defun p94b3-r-exp (ctx)
  (nth 1 ctx))

(defun p94b3-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p94b3-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p94b3-r-add-value (ctx x y)
  (p94b3-binary-value (p94b3-r-add ctx) x y))

(defun p94b3-r-neg-value (ctx x)
  (p94b3-unary-value (p94b3-r-neg ctx) x))

(defun p94b3-r-sub-value (ctx x y)
  (p94b3-r-add-value
   ctx x (p94b3-r-neg-value ctx y)))

(defun p94b3-r-mul-value (ctx x y)
  (p94b3-binary-value (p94b3-r-mul ctx) x y))

(defun p94b3-r-lt-p (ctx x y)
  (if (p94b3-binary-value (p94b3-r-lt ctx) x y)
      t nil))

(defun p94b3-r-le-p (ctx x y)
  (not (p94b3-r-lt-p ctx y x)))

(defun p94b3-r-abs-value (ctx x)
  (if (p94b3-r-lt-p ctx x (p94b3-r-zero ctx))
      (p94b3-r-neg-value ctx x)
    x))

(defun p94b3-positive-real-p (ctx x)
  (and
   (p94b3-member-p (p94b3-r-carrier ctx) x)
   (p94b3-r-lt-p ctx (p94b3-r-zero ctx) x)))

;; HasDerivAt in epsilon-delta form:
;; |f(z)-f(x)-d(z-x)| <= epsilon |z-x| near x.

(defun-sk p94b3-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (z)
    (implies
     (and
      (p94b3-member-p (p94b3-r-carrier ctx) z)
      (p94b3-r-lt-p
       ctx
       (p94b3-r-abs-value
        ctx (p94b3-r-sub-value ctx z x))
       radius))
     (p94b3-r-le-p
      ctx
      (p94b3-r-abs-value
       ctx
       (p94b3-r-sub-value
        ctx
        (p94b3-r-sub-value
         ctx
         (p94b3-unary-value function z)
         (p94b3-unary-value function x))
        (p94b3-r-mul-value
         ctx derivative
         (p94b3-r-sub-value ctx z x))))
      (p94b3-r-mul-value
       ctx epsilon
       (p94b3-r-abs-value
        ctx (p94b3-r-sub-value ctx z x)))))))

(defun-sk p94b3-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p94b3-positive-real-p ctx radius)
     (p94b3-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p94b3-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p94b3-positive-real-p ctx epsilon)
     (p94b3-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p94b3-derivative-exists-at-p
    (ctx function x)
  (exists (derivative)
    (and
     (p94b3-member-p
      (p94b3-r-carrier ctx) derivative)
     (p94b3-has-derivative-at-p
      ctx function derivative x))))

(defun-sk p94b3-differentiable-p (ctx function)
  (forall (x)
    (implies
     (p94b3-member-p (p94b3-r-carrier ctx) x)
     (p94b3-derivative-exists-at-p
      ctx function x))))

(defun-sk p94b3-exponential-derivative-values-p (ctx)
  (forall (x)
    (implies
     (p94b3-member-p (p94b3-r-carrier ctx) x)
     (p94b3-has-derivative-at-p
      ctx
      (p94b3-r-exp ctx)
      (p94b3-unary-value (p94b3-r-exp ctx) x)
      x))))

(defun p94b3-exponential-function-p (ctx)
  (and
   (tamep-functionp (p94b3-r-exp ctx))
   (p94b3-real-function-p
    (p94b3-r-carrier ctx) (p94b3-r-exp ctx))
   (equal
    (p94b3-unary-value
     (p94b3-r-exp ctx) (p94b3-r-zero ctx))
    (p94b3-r-one ctx))
   (p94b3-exponential-derivative-values-p ctx)))

(defun p94b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 2)
   (p94b3-field-context-p (p94b3-field-context ctx))
   (p94b3-exponential-function-p ctx)))

(defun-sk p94b3-growing-derivative-exists-p
    (ctx function x)
  (exists (derivative)
    (and
     (p94b3-member-p
      (p94b3-r-carrier ctx) derivative)
     (p94b3-has-derivative-at-p
      ctx function derivative x)
     (p94b3-r-lt-p
      ctx
      (p94b3-unary-value function x)
      derivative))))

(defun-sk p94b3-growing-function-points-p
    (ctx function)
  (forall (x)
    (implies
     (p94b3-member-p (p94b3-r-carrier ctx) x)
     (and
      (p94b3-positive-real-p
       ctx (p94b3-unary-value function x))
      (p94b3-growing-derivative-exists-p
       ctx function x)))))

(defun p94b3-growing-function-p (ctx function)
  (and
   (tamep-functionp function)
   (p94b3-real-function-p
    (p94b3-r-carrier ctx) function)
   (p94b3-growing-function-points-p
    ctx function)))

(defun-sk p94b3-tail-domination-p
    (ctx function k threshold)
  (forall (x)
    (implies
     (and
      (p94b3-member-p (p94b3-r-carrier ctx) x)
      (p94b3-r-lt-p ctx threshold x))
     (p94b3-r-lt-p
      ctx
      (p94b3-unary-value
       (p94b3-r-exp ctx)
       (p94b3-r-mul-value ctx k x))
      (p94b3-unary-value function x)))))

(defun-sk p94b3-threshold-exists-p
    (ctx function k)
  (exists (threshold)
    (and
     (p94b3-member-p
      (p94b3-r-carrier ctx) threshold)
     (p94b3-tail-domination-p
      ctx function k threshold))))

(defun-sk p94b3-exponent-property-p (ctx k)
  (forall (function)
    (implies
     (p94b3-growing-function-p ctx function)
     (p94b3-threshold-exists-p
      ctx function k))))

(defun-sk p94b3-solution-characterization-p (ctx)
  (forall (k)
    (implies
     (p94b3-member-p (p94b3-r-carrier ctx) k)
     (equal
      (p94b3-exponent-property-p ctx k)
      (p94b3-r-lt-p ctx k (p94b3-r-one ctx))))))

(defun putnambench-putnam-1994-b3-statement (ctx)
  (implies
   (p94b3-context-p ctx)
   (p94b3-solution-characterization-p ctx)))

(value-triple :itpeval-statement-checked)
:q
