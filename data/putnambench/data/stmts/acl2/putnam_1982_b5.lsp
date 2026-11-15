;; Statement-only formalization of PutnamBench corpus artifact putnam_1982_b5:
;; iterated real logarithms for x > e^e converge, and their pointwise limit
;; function is continuous on that open interval. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. Its exponential is characterized by
;; E' = E and E(0) = 1, and its logarithm by the standard real extension of
;; the inverse of E. Tame APPLY$ objects retain the source's arbitrary
;; real-valued sequence and limit function. All limits and continuity claims
;; are expanded into their epsilon definitions.

(defun p82b5-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p82b5-unary-value (function x)
  (apply$ function (list x)))

(defun p82b5-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p82b5-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p82b5-member-p carrier x))))

(defun-sk p82b5-real-function-p (carrier function)
  (forall (x)
    (implies
     (p82b5-member-p carrier x)
     (p82b5-member-p
      carrier
      (p82b5-unary-value function x)))))

(defun-sk p82b5-real-sequence-family-p (carrier sequence)
  (forall (x n)
    (implies
     (and
      (p82b5-member-p carrier x)
      (natp n))
     (p82b5-member-p
      carrier
      (p82b5-binary-value sequence x n)))))

(defun-sk p82b5-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p82b5-member-p carrier x)
      (p82b5-member-p carrier y)
      (p82b5-member-p carrier z))
     (and
      (p82b5-member-p carrier
                      (p82b5-binary-value add x y))
      (p82b5-member-p carrier
                      (p82b5-binary-value multiply x y))
      (p82b5-member-p carrier
                      (p82b5-unary-value negate x))
      (p82b5-member-p carrier
                      (p82b5-unary-value inverse x))
      (equal
       (p82b5-binary-value
        add (p82b5-binary-value add x y) z)
       (p82b5-binary-value
        add x (p82b5-binary-value add y z)))
      (equal
       (p82b5-binary-value add x y)
       (p82b5-binary-value add y x))
      (equal (p82b5-binary-value add x zero) x)
      (equal
       (p82b5-binary-value
        add x (p82b5-unary-value negate x))
       zero)
      (equal
       (p82b5-binary-value
        multiply (p82b5-binary-value multiply x y) z)
       (p82b5-binary-value
        multiply x (p82b5-binary-value multiply y z)))
      (equal
       (p82b5-binary-value multiply x y)
       (p82b5-binary-value multiply y x))
      (equal (p82b5-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p82b5-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p82b5-binary-value
         multiply x (p82b5-unary-value inverse x))
        one))
      (equal
       (p82b5-binary-value
        multiply x (p82b5-binary-value add y z))
       (p82b5-binary-value
        add
        (p82b5-binary-value multiply x y)
        (p82b5-binary-value multiply x z)))))))

(defun-sk p82b5-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p82b5-member-p carrier x)
      (p82b5-member-p carrier y)
      (p82b5-member-p carrier z))
     (and
      (not (p82b5-binary-value less x x))
      (or
       (equal x y)
       (p82b5-binary-value less x y)
       (p82b5-binary-value less y x))
      (implies
       (and
        (p82b5-binary-value less x y)
        (p82b5-binary-value less y z))
       (p82b5-binary-value less x z))
      (implies
       (p82b5-binary-value less x y)
       (p82b5-binary-value
        less
        (p82b5-binary-value add x z)
        (p82b5-binary-value add y z)))
      (implies
       (and
        (p82b5-binary-value less zero x)
        (p82b5-binary-value less zero y))
       (p82b5-binary-value
        less zero (p82b5-binary-value multiply x y)))))))

(defun-sk p82b5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p82b5-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p82b5-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p82b5-member-p carrier x)
      (apply$ set (list x)))
     (not (p82b5-binary-value less bound x)))))

(defun-sk p82b5-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p82b5-member-p carrier bound)
     (p82b5-upper-bound-p
      carrier less set bound))))

(defun-sk p82b5-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p82b5-member-p carrier bound)
      (p82b5-upper-bound-p carrier less set bound))
     (not (p82b5-binary-value less bound supremum)))))

(defun p82b5-supremum-p
    (carrier less set supremum)
  (and
   (p82b5-member-p carrier supremum)
   (p82b5-upper-bound-p carrier less set supremum)
   (p82b5-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p82b5-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p82b5-supremum-p
     carrier less set supremum)))

(defun-sk p82b5-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p82b5-valid-set-p carrier set)
      (p82b5-set-nonempty-p carrier set)
      (p82b5-bounded-above-p carrier less set))
     (p82b5-has-supremum-p carrier less set))))

(defun p82b5-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p82b5-member-p carrier zero)
   (p82b5-member-p carrier one)
   (not (equal zero one))
   (p82b5-field-laws-p
    carrier add multiply negate inverse zero one)
   (p82b5-order-laws-p
    carrier add multiply zero less)
   (p82b5-binary-value less zero one)
   (p82b5-dedekind-complete-p carrier less)))

;; The outer context is (field-context exponential logarithm).

(defun p82b5-field-context (ctx)
  (nth 0 ctx))

(defun p82b5-r-carrier (ctx)
  (nth 0 (p82b5-field-context ctx)))

(defun p82b5-r-zero (ctx)
  (nth 1 (p82b5-field-context ctx)))

(defun p82b5-r-one (ctx)
  (nth 2 (p82b5-field-context ctx)))

(defun p82b5-r-add (ctx)
  (nth 3 (p82b5-field-context ctx)))

(defun p82b5-r-mul (ctx)
  (nth 4 (p82b5-field-context ctx)))

(defun p82b5-r-neg (ctx)
  (nth 5 (p82b5-field-context ctx)))

(defun p82b5-r-inv (ctx)
  (nth 6 (p82b5-field-context ctx)))

(defun p82b5-r-lt (ctx)
  (nth 7 (p82b5-field-context ctx)))

(defun p82b5-r-exp (ctx)
  (nth 1 ctx))

(defun p82b5-r-log (ctx)
  (nth 2 ctx))

(defun p82b5-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p82b5-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p82b5-r-add-value (ctx x y)
  (p82b5-binary-value (p82b5-r-add ctx) x y))

(defun p82b5-r-neg-value (ctx x)
  (p82b5-unary-value (p82b5-r-neg ctx) x))

(defun p82b5-r-sub-value (ctx x y)
  (p82b5-r-add-value
   ctx x (p82b5-r-neg-value ctx y)))

(defun p82b5-r-mul-value (ctx x y)
  (p82b5-binary-value (p82b5-r-mul ctx) x y))

(defun p82b5-r-inv-value (ctx x)
  (p82b5-unary-value (p82b5-r-inv ctx) x))

(defun p82b5-r-div-value (ctx numerator denominator)
  (p82b5-r-mul-value
   ctx numerator (p82b5-r-inv-value ctx denominator)))

(defun p82b5-r-lt-p (ctx x y)
  (if (p82b5-binary-value (p82b5-r-lt ctx) x y)
      t nil))

(defun p82b5-r-le-p (ctx x y)
  (not (p82b5-r-lt-p ctx y x)))

(defun p82b5-r-abs-value (ctx x)
  (if (p82b5-r-lt-p ctx x (p82b5-r-zero ctx))
      (p82b5-r-neg-value ctx x)
    x))

(defun p82b5-positive-real-p (ctx x)
  (and
   (p82b5-member-p (p82b5-r-carrier ctx) x)
   (p82b5-r-lt-p ctx (p82b5-r-zero ctx) x)))

;; Epsilon-delta differentiability over the presented real field.

(defun-sk p82b5-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p82b5-member-p (p82b5-r-carrier ctx) y)
      (p82b5-r-lt-p
       ctx
       (p82b5-r-abs-value
        ctx (p82b5-r-sub-value ctx y x))
       radius))
     (p82b5-r-le-p
      ctx
      (p82b5-r-abs-value
       ctx
       (p82b5-r-sub-value
        ctx
        (p82b5-r-sub-value
         ctx
         (p82b5-unary-value function y)
         (p82b5-unary-value function x))
        (p82b5-r-mul-value
         ctx derivative
         (p82b5-r-sub-value ctx y x))))
      (p82b5-r-mul-value
       ctx epsilon
       (p82b5-r-abs-value
        ctx (p82b5-r-sub-value ctx y x)))))))

(defun-sk p82b5-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p82b5-positive-real-p ctx radius)
     (p82b5-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p82b5-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p82b5-positive-real-p ctx epsilon)
     (p82b5-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p82b5-global-derivative-values-p
    (ctx function derivative-function)
  (forall (x)
    (implies
     (p82b5-member-p (p82b5-r-carrier ctx) x)
     (p82b5-has-derivative-at-p
      ctx
      function
      (p82b5-unary-value derivative-function x)
      x))))

(defun p82b5-global-derivative-function-p
    (ctx function derivative-function)
  (and
   (tamep-functionp function)
   (tamep-functionp derivative-function)
   (p82b5-real-function-p
    (p82b5-r-carrier ctx) function)
   (p82b5-real-function-p
    (p82b5-r-carrier ctx) derivative-function)
   (p82b5-global-derivative-values-p
    ctx function derivative-function)))

(defun p82b5-exponential-function-p (ctx exponential)
  (and
   (p82b5-global-derivative-function-p
    ctx exponential exponential)
   (equal
    (p82b5-unary-value exponential (p82b5-r-zero ctx))
    (p82b5-r-one ctx))))

;; Real.log is zero at zero, even under negation, and is the inverse of exp
;; on the positive reals. These equations characterize the total real
;; logarithm used by Real.logb in the source statement.

(defun-sk p82b5-logarithm-laws-p
    (ctx exponential logarithm)
  (forall (x)
    (implies
     (p82b5-member-p (p82b5-r-carrier ctx) x)
     (and
      (p82b5-member-p
       (p82b5-r-carrier ctx)
       (p82b5-unary-value logarithm x))
      (p82b5-positive-real-p
       ctx (p82b5-unary-value exponential x))
      (equal
       (p82b5-unary-value
        logarithm (p82b5-unary-value exponential x))
       x)
      (implies
       (equal x (p82b5-r-zero ctx))
       (equal
        (p82b5-unary-value logarithm x)
        (p82b5-r-zero ctx)))
      (implies
       (p82b5-r-lt-p ctx x (p82b5-r-zero ctx))
       (equal
        (p82b5-unary-value logarithm x)
        (p82b5-unary-value
         logarithm (p82b5-r-neg-value ctx x))))
      (implies
       (p82b5-positive-real-p ctx x)
       (equal
        (p82b5-unary-value
         exponential (p82b5-unary-value logarithm x))
        x))))))

(defun p82b5-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 3)
   (p82b5-field-context-p (p82b5-field-context ctx))
   (tamep-functionp (p82b5-r-exp ctx))
   (tamep-functionp (p82b5-r-log ctx))
   (p82b5-exponential-function-p
    ctx (p82b5-r-exp ctx))
   (p82b5-logarithm-laws-p
    ctx (p82b5-r-exp ctx) (p82b5-r-log ctx))))

(defun p82b5-e-value (ctx)
  (p82b5-unary-value
   (p82b5-r-exp ctx) (p82b5-r-one ctx)))

(defun p82b5-threshold (ctx)
  (p82b5-unary-value
   (p82b5-r-exp ctx) (p82b5-e-value ctx)))

(defun p82b5-domain-p (ctx x)
  (and
   (p82b5-member-p (p82b5-r-carrier ctx) x)
   (p82b5-r-lt-p ctx (p82b5-threshold ctx) x)))

(defun p82b5-log-base-value (ctx base x)
  (p82b5-r-div-value
   ctx
   (p82b5-unary-value (p82b5-r-log ctx) x)
   (p82b5-unary-value (p82b5-r-log ctx) base)))

;; The source recurrence u_0 = e and u_(n+1) = log_(u_n)(x).

(defun-sk p82b5-recurrence-at-x-p (ctx sequence x)
  (forall (n)
    (implies
     (natp n)
     (equal
      (p82b5-binary-value sequence x (+ n 1))
      (p82b5-log-base-value
       ctx
       (p82b5-binary-value sequence x n)
       x)))))

(defun-sk p82b5-recurrence-p (ctx sequence)
  (forall (x)
    (implies
     (p82b5-domain-p ctx x)
     (and
      (equal
       (p82b5-binary-value sequence x 0)
       (p82b5-e-value ctx))
      (p82b5-recurrence-at-x-p
       ctx sequence x)))))

;; Sequential convergence S(x,n) -> limit.

(defun-sk p82b5-convergence-tail-p
    (ctx sequence x limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (p82b5-r-lt-p
      ctx
      (p82b5-r-abs-value
       ctx
       (p82b5-r-sub-value
        ctx
        (p82b5-binary-value sequence x n)
        limit))
      epsilon))))

(defun-sk p82b5-convergence-cutoff-exists-p
    (ctx sequence x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p82b5-convergence-tail-p
      ctx sequence x limit epsilon cutoff))))

(defun-sk p82b5-converges-to-p
    (ctx sequence x limit)
  (forall (epsilon)
    (implies
     (p82b5-positive-real-p ctx epsilon)
     (p82b5-convergence-cutoff-exists-p
      ctx sequence x limit epsilon))))

(defun-sk p82b5-limit-exists-p
    (ctx sequence x)
  (exists (limit)
    (and
     (p82b5-member-p (p82b5-r-carrier ctx) limit)
     (p82b5-converges-to-p
      ctx sequence x limit))))

(defun-sk p82b5-pointwise-limit-p
    (ctx sequence g)
  (forall (x)
    (implies
     (p82b5-domain-p ctx x)
     (p82b5-converges-to-p
      ctx sequence x (p82b5-unary-value g x)))))

;; Epsilon-delta continuity of g relative to the open domain x > e^e.

(defun-sk p82b5-continuity-neighborhood-p
    (ctx g x epsilon radius)
  (forall (y)
    (implies
     (and
      (p82b5-domain-p ctx y)
      (p82b5-r-lt-p
       ctx
       (p82b5-r-abs-value
        ctx (p82b5-r-sub-value ctx y x))
       radius))
     (p82b5-r-lt-p
      ctx
      (p82b5-r-abs-value
       ctx
       (p82b5-r-sub-value
        ctx
        (p82b5-unary-value g y)
        (p82b5-unary-value g x)))
      epsilon))))

(defun-sk p82b5-continuity-radius-exists-p
    (ctx g x epsilon)
  (exists (radius)
    (and
     (p82b5-positive-real-p ctx radius)
     (p82b5-continuity-neighborhood-p
      ctx g x epsilon radius))))

(defun-sk p82b5-continuous-within-at-p
    (ctx g x)
  (forall (epsilon)
    (implies
     (p82b5-positive-real-p ctx epsilon)
     (p82b5-continuity-radius-exists-p
      ctx g x epsilon))))

(defun-sk p82b5-continuous-on-domain-p (ctx g)
  (forall (x)
    (implies
     (p82b5-domain-p ctx x)
     (p82b5-continuous-within-at-p
      ctx g x))))

;; The source has two conclusions: the recurrence converges at every point of
;; the domain, and any function g to which it converges pointwise is continuous
;; on that domain.

(defun-sk p82b5-all-limits-exist-p (ctx sequence)
  (forall (x)
    (implies
     (p82b5-domain-p ctx x)
     (p82b5-limit-exists-p ctx sequence x))))

(defun p82b5-source-conclusion-p (ctx sequence g)
  (and
   (p82b5-all-limits-exist-p ctx sequence)
   (implies
    (p82b5-pointwise-limit-p ctx sequence g)
    (p82b5-continuous-on-domain-p ctx g))))

(defun putnambench-putnam-1982-b5-statement
    (ctx sequence g)
  (implies
   (and
    (p82b5-context-p ctx)
    (tamep-functionp sequence)
    (tamep-functionp g)
    (p82b5-real-sequence-family-p
     (p82b5-r-carrier ctx) sequence)
    (p82b5-real-function-p
     (p82b5-r-carrier ctx) g)
    (p82b5-recurrence-p ctx sequence))
   (p82b5-source-conclusion-p
    ctx sequence g)))

(value-triple :itpeval-statement-checked)
:q
