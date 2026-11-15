;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_b1:
;; a class of functions from the nonnegative reals to themselves that contains
;; exp(x)-1 and log(x+1) and is closed under addition, composition, and
;; nonnegative pointwise subtraction is closed under pointwise multiplication.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism, together with its standard
;; exponential and logarithm. Tame APPLY$ objects represent arbitrary sets
;; and functions extensionally, while DEFUN-SK keeps every unbounded
;; mathematical quantifier internal to the statement.

(defun p12b1-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p12b1-unary-value (function x)
  (apply$ function (list x)))

(defun p12b1-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p12b1-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p12b1-member-p carrier x))))

(defun-sk p12b1-real-function-p (carrier function)
  (forall (x)
    (implies
     (p12b1-member-p carrier x)
     (p12b1-member-p
      carrier
      (p12b1-unary-value function x)))))

(defun-sk p12b1-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p12b1-member-p carrier x)
      (p12b1-member-p carrier y)
      (p12b1-member-p carrier z))
     (and
      (p12b1-member-p carrier
                      (p12b1-binary-value add x y))
      (p12b1-member-p carrier
                      (p12b1-binary-value multiply x y))
      (p12b1-member-p carrier
                      (p12b1-unary-value negate x))
      (p12b1-member-p carrier
                      (p12b1-unary-value inverse x))
      (equal
       (p12b1-binary-value
        add (p12b1-binary-value add x y) z)
       (p12b1-binary-value
        add x (p12b1-binary-value add y z)))
      (equal
       (p12b1-binary-value add x y)
       (p12b1-binary-value add y x))
      (equal (p12b1-binary-value add x zero) x)
      (equal
       (p12b1-binary-value
        add x (p12b1-unary-value negate x))
       zero)
      (equal
       (p12b1-binary-value
        multiply (p12b1-binary-value multiply x y) z)
       (p12b1-binary-value
        multiply x (p12b1-binary-value multiply y z)))
      (equal
       (p12b1-binary-value multiply x y)
       (p12b1-binary-value multiply y x))
      (equal (p12b1-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p12b1-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p12b1-binary-value
         multiply x (p12b1-unary-value inverse x))
        one))
      (equal
       (p12b1-binary-value
        multiply x (p12b1-binary-value add y z))
       (p12b1-binary-value
        add
        (p12b1-binary-value multiply x y)
        (p12b1-binary-value multiply x z)))))))

(defun-sk p12b1-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p12b1-member-p carrier x)
      (p12b1-member-p carrier y)
      (p12b1-member-p carrier z))
     (and
      (not (p12b1-binary-value less x x))
      (or
       (equal x y)
       (p12b1-binary-value less x y)
       (p12b1-binary-value less y x))
      (implies
       (and
        (p12b1-binary-value less x y)
        (p12b1-binary-value less y z))
       (p12b1-binary-value less x z))
      (implies
       (p12b1-binary-value less x y)
       (p12b1-binary-value
        less
        (p12b1-binary-value add x z)
        (p12b1-binary-value add y z)))
      (implies
       (and
        (p12b1-binary-value less zero x)
        (p12b1-binary-value less zero y))
       (p12b1-binary-value
        less zero (p12b1-binary-value multiply x y)))))))

(defun-sk p12b1-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p12b1-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p12b1-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p12b1-member-p carrier x)
      (apply$ set (list x)))
     (not (p12b1-binary-value less bound x)))))

(defun-sk p12b1-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p12b1-member-p carrier bound)
     (p12b1-upper-bound-p
      carrier less set bound))))

(defun-sk p12b1-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p12b1-member-p carrier bound)
      (p12b1-upper-bound-p carrier less set bound))
     (not (p12b1-binary-value less bound supremum)))))

(defun p12b1-supremum-p
    (carrier less set supremum)
  (and
   (p12b1-member-p carrier supremum)
   (p12b1-upper-bound-p carrier less set supremum)
   (p12b1-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p12b1-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p12b1-supremum-p
     carrier less set supremum)))

(defun-sk p12b1-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p12b1-valid-set-p carrier set)
      (p12b1-set-nonempty-p carrier set)
      (p12b1-bounded-above-p carrier less set))
     (p12b1-has-supremum-p carrier less set))))

(defun p12b1-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p12b1-member-p carrier zero)
   (p12b1-member-p carrier one)
   (not (equal zero one))
   (p12b1-field-laws-p
    carrier add multiply negate inverse zero one)
   (p12b1-order-laws-p
    carrier add multiply zero less)
   (p12b1-binary-value less zero one)
   (p12b1-dedekind-complete-p carrier less)))

;; The outer context is (field-context exponential logarithm).

(defun p12b1-field-context (ctx)
  (nth 0 ctx))

(defun p12b1-r-carrier (ctx)
  (nth 0 (p12b1-field-context ctx)))

(defun p12b1-r-zero (ctx)
  (nth 1 (p12b1-field-context ctx)))

(defun p12b1-r-one (ctx)
  (nth 2 (p12b1-field-context ctx)))

(defun p12b1-r-add (ctx)
  (nth 3 (p12b1-field-context ctx)))

(defun p12b1-r-mul (ctx)
  (nth 4 (p12b1-field-context ctx)))

(defun p12b1-r-neg (ctx)
  (nth 5 (p12b1-field-context ctx)))

(defun p12b1-r-inv (ctx)
  (nth 6 (p12b1-field-context ctx)))

(defun p12b1-r-lt (ctx)
  (nth 7 (p12b1-field-context ctx)))

(defun p12b1-r-exp (ctx)
  (nth 1 ctx))

(defun p12b1-r-log (ctx)
  (nth 2 ctx))

(defun p12b1-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p12b1-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p12b1-r-add-value (ctx x y)
  (p12b1-binary-value (p12b1-r-add ctx) x y))

(defun p12b1-r-neg-value (ctx x)
  (p12b1-unary-value (p12b1-r-neg ctx) x))

(defun p12b1-r-sub-value (ctx x y)
  (p12b1-r-add-value
   ctx x (p12b1-r-neg-value ctx y)))

(defun p12b1-r-mul-value (ctx x y)
  (p12b1-binary-value (p12b1-r-mul ctx) x y))

(defun p12b1-r-inv-value (ctx x)
  (p12b1-unary-value (p12b1-r-inv ctx) x))

(defun p12b1-r-div-value (ctx numerator denominator)
  (p12b1-r-mul-value
   ctx numerator (p12b1-r-inv-value ctx denominator)))

(defun p12b1-r-lt-p (ctx x y)
  (if (p12b1-binary-value (p12b1-r-lt ctx) x y)
      t nil))

(defun p12b1-r-le-p (ctx x y)
  (not (p12b1-r-lt-p ctx y x)))

(defun p12b1-r-abs-value (ctx x)
  (if (p12b1-r-lt-p ctx x (p12b1-r-zero ctx))
      (p12b1-r-neg-value ctx x)
    x))

(defun p12b1-positive-real-p (ctx x)
  (and
   (p12b1-member-p (p12b1-r-carrier ctx) x)
   (p12b1-r-lt-p ctx (p12b1-r-zero ctx) x)))

;; HasDerivAt in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun-sk p12b1-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p12b1-member-p (p12b1-r-carrier ctx) y)
      (p12b1-r-lt-p
       ctx
       (p12b1-r-abs-value
        ctx (p12b1-r-sub-value ctx y x))
       radius))
     (p12b1-r-le-p
      ctx
      (p12b1-r-abs-value
       ctx
       (p12b1-r-sub-value
        ctx
        (p12b1-r-sub-value
         ctx
         (p12b1-unary-value function y)
         (p12b1-unary-value function x))
        (p12b1-r-mul-value
         ctx derivative
         (p12b1-r-sub-value ctx y x))))
      (p12b1-r-mul-value
       ctx epsilon
       (p12b1-r-abs-value
        ctx (p12b1-r-sub-value ctx y x)))))))

(defun-sk p12b1-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p12b1-positive-real-p ctx radius)
     (p12b1-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p12b1-derivative-epsilon-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p12b1-positive-real-p ctx epsilon)
     (p12b1-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun p12b1-has-derivative-at-p
    (ctx function derivative x)
  (and
   (p12b1-member-p (p12b1-r-carrier ctx) derivative)
   (p12b1-member-p (p12b1-r-carrier ctx) x)
   (p12b1-derivative-epsilon-p
    ctx function derivative x)))

(defun-sk p12b1-derivative-exists-at-p
    (ctx function x)
  (exists (derivative)
    (p12b1-has-derivative-at-p
     ctx function derivative x)))

(defun-sk p12b1-differentiable-on-positive-p
    (ctx function)
  (forall (x)
    (implies
     (p12b1-positive-real-p ctx x)
     (p12b1-derivative-exists-at-p
      ctx function x))))

;; The differential initial-value problem E' = E, E(0) = 1 characterizes the
;; standard real exponential. LOG is its inverse on the positive reals.

(defun-sk p12b1-exponential-laws-p (ctx)
  (forall (x)
    (implies
     (p12b1-member-p (p12b1-r-carrier ctx) x)
     (and
      (p12b1-positive-real-p
       ctx (p12b1-unary-value (p12b1-r-exp ctx) x))
      (p12b1-has-derivative-at-p
       ctx
       (p12b1-r-exp ctx)
       (p12b1-unary-value (p12b1-r-exp ctx) x)
       x)))))

(defun p12b1-exponential-function-p (ctx)
  (and
   (tamep-functionp (p12b1-r-exp ctx))
   (p12b1-real-function-p
    (p12b1-r-carrier ctx) (p12b1-r-exp ctx))
   (equal
    (p12b1-unary-value
     (p12b1-r-exp ctx) (p12b1-r-zero ctx))
    (p12b1-r-one ctx))
   (p12b1-exponential-laws-p ctx)))

(defun-sk p12b1-logarithm-laws-p (ctx)
  (forall (x)
    (implies
     (p12b1-member-p (p12b1-r-carrier ctx) x)
     (and
      (equal
       (p12b1-unary-value
        (p12b1-r-log ctx)
        (p12b1-unary-value (p12b1-r-exp ctx) x))
       x)
      (implies
       (p12b1-positive-real-p ctx x)
       (equal
        (p12b1-unary-value
         (p12b1-r-exp ctx)
         (p12b1-unary-value (p12b1-r-log ctx) x))
        x))))))

(defun p12b1-logarithm-function-p (ctx)
  (and
   (tamep-functionp (p12b1-r-log ctx))
   (p12b1-real-function-p
    (p12b1-r-carrier ctx) (p12b1-r-log ctx))
   (p12b1-logarithm-laws-p ctx)))

(defun p12b1-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 3)
   (p12b1-field-context-p (p12b1-field-context ctx))
   (p12b1-exponential-function-p ctx)
   (p12b1-logarithm-function-p ctx)))

;; Function objects on the nonnegative reals.

(defun p12b1-quoted (object)
  (list 'quote object))

(defun p12b1-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (p12b1-term-list (cdr terms)))
    (p12b1-quoted nil)))

(defun p12b1-static-apply-term (function arguments)
  (list
   'apply$
   (p12b1-quoted function)
   (p12b1-term-list arguments)))

(defun p12b1-nonnegative-real-p (ctx value)
  (and
   (p12b1-member-p (p12b1-r-carrier ctx) value)
   (p12b1-r-le-p ctx (p12b1-r-zero ctx) value)))

(defun-sk p12b1-nonnegative-function-values-p
    (ctx function)
  (forall (x)
    (implies
     (p12b1-nonnegative-real-p ctx x)
     (p12b1-nonnegative-real-p
      ctx
      (p12b1-unary-value function x)))))

(defun p12b1-nonnegative-function-p (ctx function)
  (and
   (tamep-functionp function)
   (p12b1-nonnegative-function-values-p
    ctx function)))

(defun-sk p12b1-functions-agree-p
    (ctx left right)
  (forall (x)
    (implies
     (p12b1-nonnegative-real-p ctx x)
     (equal
      (p12b1-unary-value left x)
      (p12b1-unary-value right x)))))

(defun p12b1-class-member-p (class function)
  (if (apply$ class (list function)) t nil))

(defun-sk p12b1-class-values-valid-p (ctx class)
  (forall (function)
    (implies
     (p12b1-class-member-p class function)
     (p12b1-nonnegative-function-p
      ctx function))))

(defun-sk p12b1-class-extensional-p (ctx class)
  (forall (left right)
    (implies
     (and
      (p12b1-nonnegative-function-p ctx left)
      (p12b1-nonnegative-function-p ctx right)
      (p12b1-functions-agree-p ctx left right))
     (equal
      (p12b1-class-member-p class left)
      (p12b1-class-member-p class right)))))

;; Exact pointwise function constructors.

(defun p12b1-f1-function (ctx)
  (list
   'lambda
   '(x)
   (p12b1-static-apply-term
    (p12b1-r-add ctx)
    (list
     (p12b1-static-apply-term
      (p12b1-r-exp ctx) '(x))
     (p12b1-static-apply-term
      (p12b1-r-neg ctx)
      (list
       (p12b1-quoted (p12b1-r-one ctx))))))))

(defun p12b1-f2-function (ctx)
  (list
   'lambda
   '(x)
   (p12b1-static-apply-term
    (p12b1-r-log ctx)
    (list
     (p12b1-static-apply-term
      (p12b1-r-add ctx)
      (list
       'x
       (p12b1-quoted (p12b1-r-one ctx))))))))

(defun p12b1-sum-function (ctx left right)
  (list
   'lambda
   '(x)
   (p12b1-static-apply-term
    (p12b1-r-add ctx)
    (list
     (p12b1-static-apply-term left '(x))
     (p12b1-static-apply-term right '(x))))))

(defun p12b1-compose-function (outer inner)
  (list
   'lambda
   '(x)
   (p12b1-static-apply-term
    outer
    (list
     (p12b1-static-apply-term inner '(x))))))

(defun p12b1-difference-function (ctx left right)
  (list
   'lambda
   '(x)
   (p12b1-static-apply-term
    (p12b1-r-add ctx)
    (list
     (p12b1-static-apply-term left '(x))
     (p12b1-static-apply-term
      (p12b1-r-neg ctx)
      (list
       (p12b1-static-apply-term right '(x))))))))

(defun p12b1-product-function (ctx left right)
  (list
   'lambda
   '(x)
   (p12b1-static-apply-term
    (p12b1-r-mul ctx)
    (list
     (p12b1-static-apply-term left '(x))
     (p12b1-static-apply-term right '(x))))))

;; The class hypotheses and desired closure property.

(defun-sk p12b1-addition-closed-p (ctx class)
  (forall (left right)
    (implies
     (and
      (p12b1-class-member-p class left)
      (p12b1-class-member-p class right))
     (p12b1-class-member-p
      class
      (p12b1-sum-function ctx left right)))))

(defun-sk p12b1-composition-closed-p (class)
  (forall (outer inner)
    (implies
     (and
      (p12b1-class-member-p class outer)
      (p12b1-class-member-p class inner))
     (p12b1-class-member-p
      class
      (p12b1-compose-function outer inner)))))

(defun-sk p12b1-pointwise-dominates-p
    (ctx left right)
  (forall (x)
    (implies
     (p12b1-nonnegative-real-p ctx x)
     (p12b1-r-le-p
      ctx
      (p12b1-unary-value right x)
      (p12b1-unary-value left x)))))

(defun-sk p12b1-subtraction-closed-p (ctx class)
  (forall (left right)
    (implies
     (and
      (p12b1-class-member-p class left)
      (p12b1-class-member-p class right)
      (p12b1-pointwise-dominates-p
       ctx left right))
     (p12b1-class-member-p
      class
      (p12b1-difference-function
       ctx left right)))))

(defun-sk p12b1-multiplication-closed-p (ctx class)
  (forall (left right)
    (implies
     (and
      (p12b1-class-member-p class left)
      (p12b1-class-member-p class right))
     (p12b1-class-member-p
      class
      (p12b1-product-function
       ctx left right)))))

(defun putnambench-putnam-2012-b1-statement (ctx class)
  (implies
   (and
    (p12b1-context-p ctx)
    (tamep-functionp class)
    (p12b1-class-values-valid-p ctx class)
    (p12b1-class-extensional-p ctx class)
    (p12b1-class-member-p
     class (p12b1-f1-function ctx))
    (p12b1-class-member-p
     class (p12b1-f2-function ctx))
    (p12b1-addition-closed-p ctx class)
    (p12b1-composition-closed-p class)
    (p12b1-subtraction-closed-p ctx class))
   (p12b1-multiplication-closed-p
    ctx class)))

(value-triple :itpeval-statement-checked)
:q
