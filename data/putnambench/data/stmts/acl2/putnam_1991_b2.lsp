;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_b2:
;; two nonconstant differentiable real functions satisfying the sine-cosine
;; addition laws have f(x)^2 + g(x)^2 = 1 for every real x when f'(0) = 0.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar context is a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. Arbitrary subsets and real-valued
;; functions are tame APPLY$ function objects. DEFUN-SK keeps every unbounded
;; universal and existential quantifier internal to the statement. The
;; derivative predicate is the usual epsilon-delta definition, so under the
;; explicit differentiability assumption its zero derivative clause is
;; equivalent to the source's totalized deriv f 0 = 0.

(defun p91b2-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p91b2-unary-value (function x)
  (apply$ function (list x)))

(defun p91b2-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p91b2-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p91b2-member-p carrier x))))

(defun-sk p91b2-real-function-p (carrier function)
  (forall (x)
    (implies
     (p91b2-member-p carrier x)
     (p91b2-member-p
      carrier
      (p91b2-unary-value function x)))))

(defun-sk p91b2-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p91b2-member-p carrier x)
      (p91b2-member-p carrier y)
      (p91b2-member-p carrier z))
     (and
      (p91b2-member-p carrier
                    (p91b2-binary-value add x y))
      (p91b2-member-p carrier
                    (p91b2-binary-value multiply x y))
      (p91b2-member-p carrier
                    (p91b2-unary-value negate x))
      (p91b2-member-p carrier
                    (p91b2-unary-value inverse x))
      (equal
       (p91b2-binary-value
        add (p91b2-binary-value add x y) z)
       (p91b2-binary-value
        add x (p91b2-binary-value add y z)))
      (equal (p91b2-binary-value add x y)
             (p91b2-binary-value add y x))
      (equal (p91b2-binary-value add x zero) x)
      (equal
       (p91b2-binary-value
        add x (p91b2-unary-value negate x))
       zero)
      (equal
       (p91b2-binary-value
        multiply (p91b2-binary-value multiply x y) z)
       (p91b2-binary-value
        multiply x (p91b2-binary-value multiply y z)))
      (equal (p91b2-binary-value multiply x y)
             (p91b2-binary-value multiply y x))
      (equal (p91b2-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p91b2-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p91b2-binary-value
         multiply x (p91b2-unary-value inverse x))
        one))
      (equal
       (p91b2-binary-value
        multiply x (p91b2-binary-value add y z))
       (p91b2-binary-value
        add
        (p91b2-binary-value multiply x y)
        (p91b2-binary-value multiply x z)))))))

(defun-sk p91b2-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p91b2-member-p carrier x)
      (p91b2-member-p carrier y)
      (p91b2-member-p carrier z))
     (and
      (not (p91b2-binary-value less x x))
      (or
       (equal x y)
       (p91b2-binary-value less x y)
       (p91b2-binary-value less y x))
      (implies
       (and
        (p91b2-binary-value less x y)
        (p91b2-binary-value less y z))
       (p91b2-binary-value less x z))
      (implies
       (p91b2-binary-value less x y)
       (p91b2-binary-value
        less
        (p91b2-binary-value add x z)
        (p91b2-binary-value add y z)))
      (implies
       (and
        (p91b2-binary-value less zero x)
        (p91b2-binary-value less zero y))
       (p91b2-binary-value
        less zero (p91b2-binary-value multiply x y)))))))

(defun-sk p91b2-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p91b2-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p91b2-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p91b2-member-p carrier x)
      (apply$ set (list x)))
     (not (p91b2-binary-value less bound x)))))

(defun-sk p91b2-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p91b2-member-p carrier bound)
     (p91b2-upper-bound-p
      carrier less set bound))))

(defun-sk p91b2-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p91b2-member-p carrier bound)
      (p91b2-upper-bound-p carrier less set bound))
     (not (p91b2-binary-value less bound supremum)))))

(defun p91b2-supremum-p
    (carrier less set supremum)
  (and
   (p91b2-member-p carrier supremum)
   (p91b2-upper-bound-p carrier less set supremum)
   (p91b2-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p91b2-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p91b2-supremum-p
     carrier less set supremum)))

(defun-sk p91b2-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p91b2-valid-set-p carrier set)
      (p91b2-set-nonempty-p carrier set)
      (p91b2-bounded-above-p carrier less set))
     (p91b2-has-supremum-p carrier less set))))

(defun p91b2-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p91b2-member-p carrier zero)
   (p91b2-member-p carrier one)
   (not (equal zero one))
   (p91b2-field-laws-p
    carrier add multiply negate inverse zero one)
   (p91b2-order-laws-p
    carrier add multiply zero less)
   (p91b2-binary-value less zero one)
   (p91b2-dedekind-complete-p carrier less)))

;; The outer context contains one eight-entry real-field presentation.

(defun p91b2-field-context (ctx)
  (car ctx))

(defun p91b2-r-carrier (ctx)
  (nth 0 (p91b2-field-context ctx)))

(defun p91b2-r-zero (ctx)
  (nth 1 (p91b2-field-context ctx)))

(defun p91b2-r-one (ctx)
  (nth 2 (p91b2-field-context ctx)))

(defun p91b2-r-add (ctx)
  (nth 3 (p91b2-field-context ctx)))

(defun p91b2-r-mul (ctx)
  (nth 4 (p91b2-field-context ctx)))

(defun p91b2-r-neg (ctx)
  (nth 5 (p91b2-field-context ctx)))

(defun p91b2-r-inv (ctx)
  (nth 6 (p91b2-field-context ctx)))

(defun p91b2-r-lt (ctx)
  (nth 7 (p91b2-field-context ctx)))

(defun p91b2-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p91b2-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p91b2-r-add-value (ctx x y)
  (p91b2-binary-value (p91b2-r-add ctx) x y))

(defun p91b2-r-neg-value (ctx x)
  (p91b2-unary-value (p91b2-r-neg ctx) x))

(defun p91b2-r-sub-value (ctx x y)
  (p91b2-r-add-value
   ctx x (p91b2-r-neg-value ctx y)))

(defun p91b2-r-mul-value (ctx x y)
  (p91b2-binary-value (p91b2-r-mul ctx) x y))

(defun p91b2-r-lt-p (ctx x y)
  (if (p91b2-binary-value (p91b2-r-lt ctx) x y)
      t nil))

(defun p91b2-r-le-p (ctx x y)
  (not (p91b2-r-lt-p ctx y x)))

(defun p91b2-r-abs-value (ctx x)
  (if (p91b2-r-lt-p ctx x (p91b2-r-zero ctx))
      (p91b2-r-neg-value ctx x)
    x))

(defun p91b2-positive-real-p (ctx x)
  (and
   (p91b2-member-p (p91b2-r-carrier ctx) x)
   (p91b2-r-lt-p ctx (p91b2-r-zero ctx) x)))

;; HasDerivAt in epsilon-delta form:
;; |f(z)-f(x)-d(z-x)| <= epsilon |z-x| near x.

(defun-sk p91b2-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (z)
    (implies
     (and
      (p91b2-member-p (p91b2-r-carrier ctx) z)
      (p91b2-r-lt-p
       ctx
       (p91b2-r-abs-value
        ctx (p91b2-r-sub-value ctx z x))
       radius))
     (p91b2-r-le-p
      ctx
      (p91b2-r-abs-value
       ctx
       (p91b2-r-sub-value
        ctx
        (p91b2-r-sub-value
         ctx
         (p91b2-unary-value function z)
         (p91b2-unary-value function x))
        (p91b2-r-mul-value
         ctx derivative
         (p91b2-r-sub-value ctx z x))))
      (p91b2-r-mul-value
       ctx epsilon
       (p91b2-r-abs-value
        ctx (p91b2-r-sub-value ctx z x)))))))

(defun-sk p91b2-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p91b2-positive-real-p ctx radius)
     (p91b2-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p91b2-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p91b2-positive-real-p ctx epsilon)
     (p91b2-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p91b2-derivative-exists-at-p
    (ctx function x)
  (exists (derivative)
    (and
     (p91b2-member-p
      (p91b2-r-carrier ctx) derivative)
     (p91b2-has-derivative-at-p
      ctx function derivative x))))

(defun-sk p91b2-differentiable-p (ctx function)
  (forall (x)
    (implies
     (p91b2-member-p (p91b2-r-carrier ctx) x)
     (p91b2-derivative-exists-at-p
      ctx function x))))

(defun p91b2-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 1)
   (p91b2-field-context-p (p91b2-field-context ctx))))

(defun-sk p91b2-constant-with-value-p
    (ctx function constant)
  (forall (x)
    (implies
     (p91b2-member-p (p91b2-r-carrier ctx) x)
     (equal
      (p91b2-unary-value function x)
      constant))))

(defun-sk p91b2-constant-function-p (ctx function)
  (exists (constant)
    (and
     (p91b2-member-p
      (p91b2-r-carrier ctx) constant)
     (p91b2-constant-with-value-p
      ctx function constant))))

(defun-sk p91b2-addition-laws-p (ctx f g)
  (forall (x y)
    (implies
     (and
      (p91b2-member-p (p91b2-r-carrier ctx) x)
      (p91b2-member-p (p91b2-r-carrier ctx) y))
     (and
      (equal
       (p91b2-unary-value
        f (p91b2-r-add-value ctx x y))
       (p91b2-r-sub-value
        ctx
        (p91b2-r-mul-value
         ctx
         (p91b2-unary-value f x)
         (p91b2-unary-value f y))
        (p91b2-r-mul-value
         ctx
         (p91b2-unary-value g x)
         (p91b2-unary-value g y))))
      (equal
       (p91b2-unary-value
        g (p91b2-r-add-value ctx x y))
       (p91b2-r-add-value
        ctx
        (p91b2-r-mul-value
         ctx
         (p91b2-unary-value f x)
         (p91b2-unary-value g y))
        (p91b2-r-mul-value
         ctx
         (p91b2-unary-value g x)
         (p91b2-unary-value f y))))))))

(defun-sk p91b2-unit-circle-identity-p (ctx f g)
  (forall (x)
    (implies
     (p91b2-member-p (p91b2-r-carrier ctx) x)
     (equal
      (p91b2-r-add-value
       ctx
       (p91b2-r-mul-value
        ctx
        (p91b2-unary-value f x)
        (p91b2-unary-value f x))
       (p91b2-r-mul-value
        ctx
        (p91b2-unary-value g x)
        (p91b2-unary-value g x)))
      (p91b2-r-one ctx)))))

(defun putnambench-putnam-1991-b2-statement (ctx f g)
  (implies
   (and
    (p91b2-context-p ctx)
    (tamep-functionp f)
    (tamep-functionp g)
    (p91b2-real-function-p
     (p91b2-r-carrier ctx) f)
    (p91b2-real-function-p
     (p91b2-r-carrier ctx) g)
    (not (p91b2-constant-function-p ctx f))
    (not (p91b2-constant-function-p ctx g))
    (p91b2-differentiable-p ctx f)
    (p91b2-differentiable-p ctx g)
    (p91b2-addition-laws-p ctx f g)
    (p91b2-has-derivative-at-p
     ctx f (p91b2-r-zero ctx) (p91b2-r-zero ctx)))
   (p91b2-unit-circle-identity-p ctx f g)))

(value-triple :itpeval-statement-checked)
:q
