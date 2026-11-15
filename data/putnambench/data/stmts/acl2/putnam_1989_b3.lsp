;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_b3:
;; moments of a differentiable, rapidly decaying solution of a real
;; differential-dilation equation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism, together with its exponential and
;; nonnegative square-root functions. Tame APPLY$ objects represent the
;; arbitrary function and moment sequence. DEFUN-SK keeps all unbounded
;; mathematical quantifiers and analytic witnesses internal to the statement.

(defun p89b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p89b3-unary-value (function x)
  (apply$ function (list x)))

(defun p89b3-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p89b3-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p89b3-member-p carrier x))))

(defun-sk p89b3-real-function-p (carrier function)
  (forall (x)
    (implies
     (p89b3-member-p carrier x)
     (p89b3-member-p
      carrier
      (p89b3-unary-value function x)))))

(defun-sk p89b3-real-sequence-p (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (p89b3-member-p
      carrier
      (p89b3-unary-value sequence n)))))

(defun-sk p89b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p89b3-member-p carrier x)
      (p89b3-member-p carrier y)
      (p89b3-member-p carrier z))
     (and
      (p89b3-member-p carrier
                      (p89b3-binary-value add x y))
      (p89b3-member-p carrier
                      (p89b3-binary-value multiply x y))
      (p89b3-member-p carrier
                      (p89b3-unary-value negate x))
      (p89b3-member-p carrier
                      (p89b3-unary-value inverse x))
      (equal
       (p89b3-binary-value
        add (p89b3-binary-value add x y) z)
       (p89b3-binary-value
        add x (p89b3-binary-value add y z)))
      (equal
       (p89b3-binary-value add x y)
       (p89b3-binary-value add y x))
      (equal (p89b3-binary-value add x zero) x)
      (equal
       (p89b3-binary-value
        add x (p89b3-unary-value negate x))
       zero)
      (equal
       (p89b3-binary-value
        multiply (p89b3-binary-value multiply x y) z)
       (p89b3-binary-value
        multiply x (p89b3-binary-value multiply y z)))
      (equal
       (p89b3-binary-value multiply x y)
       (p89b3-binary-value multiply y x))
      (equal (p89b3-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p89b3-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p89b3-binary-value
         multiply x (p89b3-unary-value inverse x))
        one))
      (equal
       (p89b3-binary-value
        multiply x (p89b3-binary-value add y z))
       (p89b3-binary-value
        add
        (p89b3-binary-value multiply x y)
        (p89b3-binary-value multiply x z)))))))

(defun-sk p89b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p89b3-member-p carrier x)
      (p89b3-member-p carrier y)
      (p89b3-member-p carrier z))
     (and
      (not (p89b3-binary-value less x x))
      (or
       (equal x y)
       (p89b3-binary-value less x y)
       (p89b3-binary-value less y x))
      (implies
       (and
        (p89b3-binary-value less x y)
        (p89b3-binary-value less y z))
       (p89b3-binary-value less x z))
      (implies
       (p89b3-binary-value less x y)
       (p89b3-binary-value
        less
        (p89b3-binary-value add x z)
        (p89b3-binary-value add y z)))
      (implies
       (and
        (p89b3-binary-value less zero x)
        (p89b3-binary-value less zero y))
       (p89b3-binary-value
        less zero (p89b3-binary-value multiply x y)))))))

(defun-sk p89b3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p89b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p89b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p89b3-member-p carrier x)
      (apply$ set (list x)))
     (not (p89b3-binary-value less bound x)))))

(defun-sk p89b3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p89b3-member-p carrier bound)
     (p89b3-upper-bound-p carrier less set bound))))

(defun-sk p89b3-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p89b3-member-p carrier bound)
      (p89b3-upper-bound-p carrier less set bound))
     (not (p89b3-binary-value less bound supremum)))))

(defun p89b3-supremum-p
    (carrier less set supremum)
  (and
   (p89b3-member-p carrier supremum)
   (p89b3-upper-bound-p carrier less set supremum)
   (p89b3-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p89b3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p89b3-supremum-p carrier less set supremum)))

(defun-sk p89b3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p89b3-valid-set-p carrier set)
      (p89b3-set-nonempty-p carrier set)
      (p89b3-bounded-above-p carrier less set))
     (p89b3-has-supremum-p carrier less set))))

(defun p89b3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p89b3-member-p carrier zero)
   (p89b3-member-p carrier one)
   (not (equal zero one))
   (p89b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p89b3-order-laws-p
    carrier add multiply zero less)
   (p89b3-binary-value less zero one)
   (p89b3-dedekind-complete-p carrier less)))

;; The outer context is (field-context exponential square-root).

(defun p89b3-field-context (ctx)
  (nth 0 ctx))

(defun p89b3-r-carrier (ctx)
  (nth 0 (p89b3-field-context ctx)))

(defun p89b3-r-zero (ctx)
  (nth 1 (p89b3-field-context ctx)))

(defun p89b3-r-one (ctx)
  (nth 2 (p89b3-field-context ctx)))

(defun p89b3-r-add (ctx)
  (nth 3 (p89b3-field-context ctx)))

(defun p89b3-r-mul (ctx)
  (nth 4 (p89b3-field-context ctx)))

(defun p89b3-r-neg (ctx)
  (nth 5 (p89b3-field-context ctx)))

(defun p89b3-r-inv (ctx)
  (nth 6 (p89b3-field-context ctx)))

(defun p89b3-r-lt (ctx)
  (nth 7 (p89b3-field-context ctx)))

(defun p89b3-r-exp (ctx)
  (nth 1 ctx))

(defun p89b3-r-sqrt (ctx)
  (nth 2 ctx))

(defun p89b3-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p89b3-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p89b3-r-add-value (ctx x y)
  (p89b3-binary-value (p89b3-r-add ctx) x y))

(defun p89b3-r-neg-value (ctx x)
  (p89b3-unary-value (p89b3-r-neg ctx) x))

(defun p89b3-r-sub-value (ctx x y)
  (p89b3-r-add-value
   ctx x (p89b3-r-neg-value ctx y)))

(defun p89b3-r-mul-value (ctx x y)
  (p89b3-binary-value (p89b3-r-mul ctx) x y))

(defun p89b3-r-inv-value (ctx x)
  (p89b3-unary-value (p89b3-r-inv ctx) x))

(defun p89b3-r-div-value (ctx numerator denominator)
  (p89b3-r-mul-value
   ctx numerator (p89b3-r-inv-value ctx denominator)))

(defun p89b3-r-lt-p (ctx x y)
  (if (p89b3-binary-value (p89b3-r-lt ctx) x y)
      t nil))

(defun p89b3-r-le-p (ctx x y)
  (not (p89b3-r-lt-p ctx y x)))

(defun p89b3-r-abs-value (ctx x)
  (if (p89b3-r-lt-p ctx x (p89b3-r-zero ctx))
      (p89b3-r-neg-value ctx x)
    x))

(defun p89b3-positive-real-p (ctx x)
  (and
   (p89b3-member-p (p89b3-r-carrier ctx) x)
   (p89b3-r-lt-p ctx (p89b3-r-zero ctx) x)))

(defun p89b3-nonnegative-real-p (ctx x)
  (and
   (p89b3-member-p (p89b3-r-carrier ctx) x)
   (p89b3-r-le-p ctx (p89b3-r-zero ctx) x)))

(defun p89b3-r-nat (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p89b3-r-zero ctx)
    (p89b3-r-add-value
     ctx
     (p89b3-r-one ctx)
     (p89b3-r-nat ctx (1- n)))))

(defun p89b3-r-pow (ctx x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p89b3-r-one ctx)
    (p89b3-r-mul-value
     ctx x (p89b3-r-pow ctx x (1- n)))))

(defun p89b3-r-factorial (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p89b3-r-one ctx)
    (p89b3-r-mul-value
     ctx
     (p89b3-r-nat ctx n)
     (p89b3-r-factorial ctx (1- n)))))

(defun p89b3-solution-product (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p89b3-r-one ctx)
    (p89b3-r-mul-value
     ctx
     (p89b3-solution-product ctx (1- n))
     (p89b3-r-sub-value
      ctx
      (p89b3-r-one ctx)
      (p89b3-r-inv-value
       ctx
       (p89b3-r-pow
        ctx (p89b3-r-nat ctx 2) n))))))

(defun p89b3-solution-value (ctx n c)
  (p89b3-r-div-value
   ctx
   (p89b3-r-mul-value
    ctx c (p89b3-r-factorial ctx n))
   (p89b3-r-mul-value
    ctx
    (p89b3-r-pow
     ctx (p89b3-r-nat ctx 3) n)
    (p89b3-solution-product ctx n))))

(defun p89b3-normalized-value (ctx moments n)
  (p89b3-r-div-value
   ctx
   (p89b3-r-mul-value
    ctx
    (p89b3-unary-value moments n)
    (p89b3-r-pow
     ctx (p89b3-r-nat ctx 3) n))
   (p89b3-r-factorial ctx n)))

;; Global epsilon-delta derivatives characterize the exponential function.

(defun-sk p89b3-global-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p89b3-member-p (p89b3-r-carrier ctx) y)
      (p89b3-r-lt-p
       ctx
       (p89b3-r-abs-value
        ctx (p89b3-r-sub-value ctx y x))
       radius))
     (p89b3-r-le-p
      ctx
      (p89b3-r-abs-value
       ctx
       (p89b3-r-sub-value
        ctx
        (p89b3-r-sub-value
         ctx
         (p89b3-unary-value function y)
         (p89b3-unary-value function x))
        (p89b3-r-mul-value
         ctx derivative
         (p89b3-r-sub-value ctx y x))))
      (p89b3-r-mul-value
       ctx epsilon
       (p89b3-r-abs-value
        ctx (p89b3-r-sub-value ctx y x)))))))

(defun-sk p89b3-global-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p89b3-positive-real-p ctx radius)
     (p89b3-global-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p89b3-has-global-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p89b3-positive-real-p ctx epsilon)
     (p89b3-global-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p89b3-global-derivative-values-p
    (ctx function derivative-function)
  (forall (x)
    (implies
     (p89b3-member-p (p89b3-r-carrier ctx) x)
     (p89b3-has-global-derivative-at-p
      ctx
      function
      (p89b3-unary-value derivative-function x)
      x))))

(defun p89b3-global-derivative-function-p
    (ctx function derivative-function)
  (and
   (tamep-functionp function)
   (tamep-functionp derivative-function)
   (p89b3-real-function-p
    (p89b3-r-carrier ctx) function)
   (p89b3-real-function-p
    (p89b3-r-carrier ctx) derivative-function)
   (p89b3-global-derivative-values-p
    ctx function derivative-function)))

(defun p89b3-exponential-function-p (ctx exponential)
  (and
   (p89b3-global-derivative-function-p
    ctx exponential exponential)
   (equal
    (p89b3-unary-value exponential (p89b3-r-zero ctx))
    (p89b3-r-one ctx))))

(defun-sk p89b3-square-root-laws-p (ctx square-root)
  (forall (x)
    (implies
     (p89b3-member-p (p89b3-r-carrier ctx) x)
     (and
      (p89b3-member-p
       (p89b3-r-carrier ctx)
       (p89b3-unary-value square-root x))
      (implies
       (p89b3-r-le-p ctx (p89b3-r-zero ctx) x)
       (and
        (p89b3-r-le-p
         ctx
         (p89b3-r-zero ctx)
         (p89b3-unary-value square-root x))
        (equal
         (p89b3-r-mul-value
          ctx
          (p89b3-unary-value square-root x)
          (p89b3-unary-value square-root x))
         x)))))))

(defun p89b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 3)
   (p89b3-field-context-p (p89b3-field-context ctx))
   (tamep-functionp (p89b3-r-exp ctx))
   (tamep-functionp (p89b3-r-sqrt ctx))
   (p89b3-exponential-function-p
    ctx (p89b3-r-exp ctx))
   (p89b3-square-root-laws-p
    ctx (p89b3-r-sqrt ctx))))

;; Differentiability relative to [0,infinity). At positive points this is the
;; usual derivative because they are interior points of the half-line.

(defun-sk p89b3-relative-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p89b3-nonnegative-real-p ctx y)
      (p89b3-r-lt-p
       ctx
       (p89b3-r-abs-value
        ctx (p89b3-r-sub-value ctx y x))
       radius))
     (p89b3-r-le-p
      ctx
      (p89b3-r-abs-value
       ctx
       (p89b3-r-sub-value
        ctx
        (p89b3-r-sub-value
         ctx
         (p89b3-unary-value function y)
         (p89b3-unary-value function x))
        (p89b3-r-mul-value
         ctx derivative
         (p89b3-r-sub-value ctx y x))))
      (p89b3-r-mul-value
       ctx epsilon
       (p89b3-r-abs-value
        ctx (p89b3-r-sub-value ctx y x)))))))

(defun-sk p89b3-relative-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p89b3-positive-real-p ctx radius)
     (p89b3-relative-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p89b3-has-relative-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p89b3-positive-real-p ctx epsilon)
     (p89b3-relative-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p89b3-relative-derivative-exists-at-p
    (ctx function x)
  (exists (derivative)
    (and
     (p89b3-member-p (p89b3-r-carrier ctx) derivative)
     (p89b3-has-relative-derivative-at-p
      ctx function derivative x))))

(defun-sk p89b3-differentiable-on-nonnegative-p
    (ctx function)
  (forall (x)
    (implies
     (p89b3-nonnegative-real-p ctx x)
     (p89b3-relative-derivative-exists-at-p
      ctx function x))))

(defun p89b3-differential-equation-value (ctx function x)
  (p89b3-r-add-value
   ctx
   (p89b3-r-mul-value
    ctx
    (p89b3-r-neg-value
     ctx (p89b3-r-nat ctx 3))
    (p89b3-unary-value function x))
   (p89b3-r-mul-value
    ctx
    (p89b3-r-nat ctx 6)
    (p89b3-unary-value
     function
     (p89b3-r-mul-value
      ctx (p89b3-r-nat ctx 2) x)))))

(defun-sk p89b3-differential-equation-p
    (ctx function)
  (forall (x)
    (implies
     (p89b3-positive-real-p ctx x)
     (p89b3-has-relative-derivative-at-p
      ctx
      function
      (p89b3-differential-equation-value
       ctx function x)
      x))))

(defun-sk p89b3-decay-bound-p (ctx function)
  (forall (x)
    (implies
     (p89b3-nonnegative-real-p ctx x)
     (p89b3-r-le-p
      ctx
      (p89b3-r-abs-value
       ctx (p89b3-unary-value function x))
      (p89b3-unary-value
       (p89b3-r-exp ctx)
       (p89b3-r-neg-value
        ctx
        (p89b3-unary-value
         (p89b3-r-sqrt ctx) x)))))))

;; On each bounded interval the moment is the limit of uniform left Riemann
;; sums. Differentiability makes the integrand continuous there, so this is
;; equal to the source Lebesgue integral. The outer limit is the improper
;; integral over (0,infinity).

(defun p89b3-riemann-width (ctx subdivisions radius)
  (p89b3-r-div-value
   ctx radius (p89b3-r-nat ctx subdivisions)))

(defun p89b3-riemann-point
    (ctx index subdivisions radius)
  (p89b3-r-mul-value
   ctx
   (p89b3-r-nat ctx index)
   (p89b3-riemann-width ctx subdivisions radius)))

(defun p89b3-moment-integrand-value
    (ctx function n x)
  (p89b3-r-mul-value
   ctx
   (p89b3-r-pow ctx x n)
   (p89b3-unary-value function x)))

(defun p89b3-riemann-sum-aux
    (ctx remaining subdivisions radius function n)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p89b3-r-zero ctx)
    (let* ((index (1- remaining))
           (width
            (p89b3-riemann-width
             ctx subdivisions radius))
           (point
            (p89b3-riemann-point
             ctx index subdivisions radius))
           (summand
            (p89b3-r-mul-value
             ctx
             width
             (p89b3-moment-integrand-value
              ctx function n point))))
      (p89b3-r-add-value
       ctx
       (p89b3-riemann-sum-aux
        ctx index subdivisions radius function n)
       summand))))

(defun p89b3-riemann-sum
    (ctx subdivisions radius function n)
  (if (posp subdivisions)
      (p89b3-riemann-sum-aux
       ctx subdivisions subdivisions radius function n)
    (p89b3-r-zero ctx)))

(defun-sk p89b3-riemann-tail-p
    (ctx function n radius value epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p89b3-r-lt-p
      ctx
      (p89b3-r-abs-value
       ctx
       (p89b3-r-sub-value
        ctx
        (p89b3-riemann-sum
         ctx subdivisions radius function n)
        value))
      epsilon))))

(defun-sk p89b3-riemann-cutoff-exists-p
    (ctx function n radius value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p89b3-riemann-tail-p
      ctx function n radius value epsilon cutoff))))

(defun-sk p89b3-bounded-moment-integral-p
    (ctx function n radius value)
  (forall (epsilon)
    (implies
     (p89b3-positive-real-p ctx epsilon)
     (p89b3-riemann-cutoff-exists-p
      ctx function n radius value epsilon))))

(defun-sk p89b3-moment-at-radius-close-p
    (ctx function n radius limit epsilon)
  (exists (value)
    (and
     (p89b3-member-p (p89b3-r-carrier ctx) value)
     (p89b3-bounded-moment-integral-p
      ctx function n radius value)
     (p89b3-r-lt-p
      ctx
      (p89b3-r-abs-value
       ctx (p89b3-r-sub-value ctx value limit))
      epsilon))))

(defun-sk p89b3-improper-moment-tail-p
    (ctx function n limit epsilon cutoff)
  (forall (radius)
    (implies
     (and
      (p89b3-nonnegative-real-p ctx radius)
      (p89b3-r-le-p ctx cutoff radius))
     (p89b3-moment-at-radius-close-p
      ctx function n radius limit epsilon))))

(defun-sk p89b3-improper-moment-cutoff-exists-p
    (ctx function n limit epsilon)
  (exists (cutoff)
    (and
     (p89b3-positive-real-p ctx cutoff)
     (p89b3-improper-moment-tail-p
      ctx function n limit epsilon cutoff))))

(defun-sk p89b3-improper-moment-p
    (ctx function n limit)
  (forall (epsilon)
    (implies
     (p89b3-positive-real-p ctx epsilon)
     (p89b3-improper-moment-cutoff-exists-p
      ctx function n limit epsilon))))

(defun-sk p89b3-moments-definition-p
    (ctx function moments)
  (forall (n)
    (implies
     (natp n)
     (p89b3-improper-moment-p
      ctx
      function
      n
      (p89b3-unary-value moments n)))))

(defun-sk p89b3-solution-formula-p (ctx moments)
  (forall (n)
    (implies
     (natp n)
     (equal
      (p89b3-unary-value moments n)
      (p89b3-solution-value
       ctx n (p89b3-unary-value moments 0))))))

(defun-sk p89b3-normalized-convergence-tail-p
    (ctx moments limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (p89b3-r-lt-p
      ctx
      (p89b3-r-abs-value
       ctx
       (p89b3-r-sub-value
        ctx
        (p89b3-normalized-value ctx moments n)
        limit))
      epsilon))))

(defun-sk p89b3-normalized-convergence-cutoff-exists-p
    (ctx moments limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p89b3-normalized-convergence-tail-p
      ctx moments limit epsilon cutoff))))

(defun-sk p89b3-normalized-converges-to-p
    (ctx moments limit)
  (forall (epsilon)
    (implies
     (p89b3-positive-real-p ctx epsilon)
     (p89b3-normalized-convergence-cutoff-exists-p
      ctx moments limit epsilon))))

(defun-sk p89b3-normalized-limit-exists-p
    (ctx moments)
  (exists (limit)
    (and
     (p89b3-member-p (p89b3-r-carrier ctx) limit)
     (p89b3-normalized-converges-to-p
      ctx moments limit))))

(defun putnambench-putnam-1989-b3-statement
    (ctx function moments)
  (implies
   (and
    (p89b3-context-p ctx)
    (tamep-functionp function)
    (tamep-functionp moments)
    (p89b3-real-function-p
     (p89b3-r-carrier ctx) function)
    (p89b3-real-sequence-p
     (p89b3-r-carrier ctx) moments)
    (p89b3-differentiable-on-nonnegative-p
     ctx function)
    (p89b3-differential-equation-p
     ctx function)
    (p89b3-decay-bound-p
     ctx function)
    (p89b3-moments-definition-p
     ctx function moments))
   (and
    (p89b3-solution-formula-p ctx moments)
    (p89b3-normalized-limit-exists-p ctx moments)
    (implies
     (p89b3-normalized-converges-to-p
      ctx moments (p89b3-r-zero ctx))
     (equal
      (p89b3-unary-value moments 0)
      (p89b3-r-zero ctx))))))

(value-triple :itpeval-statement-checked)
:q
