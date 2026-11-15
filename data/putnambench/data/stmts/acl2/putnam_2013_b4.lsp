;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_b4:
;; the variance of the pointwise product of two continuous real functions on
;; [0,1] is bounded by the stated combination of their variances and maximum
;; absolute values. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. APPLY$ objects represent arbitrary
;; real functions, and DEFUN-SK keeps all function, integral, mean, variance,
;; and maximum witnesses at their source quantifier scopes. Continuity is the
;; relative epsilon-delta definition on [0,1]. For continuous functions, the
;; unbounded uniform right-endpoint Riemann-sum limit below equals the source
;; interval integral, and the maximum predicate includes both attainment and
;; the universal upper-bound property.

(defun p13b4-quoted (object)
  (list 'quote object))

(defun p13b4-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (p13b4-term-list (cdr terms)))
    (p13b4-quoted nil)))

(defun p13b4-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (p13b4-term-list arguments)))

(defun p13b4-static-apply-term (function arguments)
  (p13b4-apply-term
   (p13b4-quoted function)
   arguments))

(defun p13b4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p13b4-unary-value (operation x)
  (apply$ operation (list x)))

(defun p13b4-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p13b4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p13b4-member-p carrier x))))

(defun-sk p13b4-real-function-p (carrier function)
  (forall (x)
    (implies
     (p13b4-member-p carrier x)
     (p13b4-member-p
      carrier
      (p13b4-unary-value function x)))))

;; A Dedekind-complete ordered field presents the real scalar structure.

(defun-sk p13b4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p13b4-member-p carrier x)
      (p13b4-member-p carrier y)
      (p13b4-member-p carrier z))
     (and
      (p13b4-member-p
       carrier (p13b4-binary-value add x y))
      (p13b4-member-p
       carrier (p13b4-binary-value multiply x y))
      (p13b4-member-p
       carrier (p13b4-unary-value negate x))
      (p13b4-member-p
       carrier (p13b4-unary-value inverse x))
      (equal
       (p13b4-binary-value
        add (p13b4-binary-value add x y) z)
       (p13b4-binary-value
        add x (p13b4-binary-value add y z)))
      (equal
       (p13b4-binary-value add x y)
       (p13b4-binary-value add y x))
      (equal (p13b4-binary-value add x zero) x)
      (equal
       (p13b4-binary-value
        add x (p13b4-unary-value negate x))
       zero)
      (equal
       (p13b4-binary-value
        multiply
        (p13b4-binary-value multiply x y)
        z)
       (p13b4-binary-value
        multiply
        x
        (p13b4-binary-value multiply y z)))
      (equal
       (p13b4-binary-value multiply x y)
       (p13b4-binary-value multiply y x))
      (equal
       (p13b4-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p13b4-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p13b4-binary-value
         multiply x (p13b4-unary-value inverse x))
        one))
      (equal
       (p13b4-binary-value
        multiply x (p13b4-binary-value add y z))
       (p13b4-binary-value
        add
        (p13b4-binary-value multiply x y)
        (p13b4-binary-value multiply x z)))))))

(defun-sk p13b4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p13b4-member-p carrier x)
      (p13b4-member-p carrier y)
      (p13b4-member-p carrier z))
     (and
      (not (p13b4-binary-value less x x))
      (or
       (equal x y)
       (p13b4-binary-value less x y)
       (p13b4-binary-value less y x))
      (implies
       (and
        (p13b4-binary-value less x y)
        (p13b4-binary-value less y z))
       (p13b4-binary-value less x z))
      (implies
       (p13b4-binary-value less x y)
       (p13b4-binary-value
        less
        (p13b4-binary-value add x z)
        (p13b4-binary-value add y z)))
      (implies
       (and
        (p13b4-binary-value less zero x)
        (p13b4-binary-value less zero y))
       (p13b4-binary-value
        less
        zero
        (p13b4-binary-value multiply x y)))))))

(defun-sk p13b4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p13b4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p13b4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p13b4-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p13b4-binary-value less bound x)))))

(defun-sk p13b4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p13b4-member-p carrier bound)
     (p13b4-upper-bound-p
      carrier less set bound))))

(defun-sk p13b4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p13b4-member-p carrier bound)
      (p13b4-upper-bound-p
       carrier less set bound))
     (not
      (p13b4-binary-value
       less bound supremum)))))

(defun p13b4-supremum-p
    (carrier less set supremum)
  (and
   (p13b4-member-p carrier supremum)
   (p13b4-upper-bound-p
    carrier less set supremum)
   (p13b4-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p13b4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p13b4-supremum-p
     carrier less set supremum)))

(defun-sk p13b4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p13b4-valid-set-p carrier set)
      (p13b4-set-nonempty-p carrier set)
      (p13b4-bounded-above-p carrier less set))
     (p13b4-has-supremum-p
      carrier less set))))

(defun p13b4-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p13b4-member-p carrier zero)
   (p13b4-member-p carrier one)
   (not (equal zero one))
   (p13b4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p13b4-order-laws-p
    carrier add multiply zero less)
   (p13b4-binary-value less zero one)
   (p13b4-dedekind-complete-p carrier less)))

;; Real-field context and arithmetic.

(defun p13b4-r-carrier (ctx) (nth 0 ctx))
(defun p13b4-r-zero (ctx) (nth 1 ctx))
(defun p13b4-r-one (ctx) (nth 2 ctx))
(defun p13b4-r-add (ctx) (nth 3 ctx))
(defun p13b4-r-mul (ctx) (nth 4 ctx))
(defun p13b4-r-neg (ctx) (nth 5 ctx))
(defun p13b4-r-inv (ctx) (nth 6 ctx))
(defun p13b4-r-lt (ctx) (nth 7 ctx))

(defun p13b4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p13b4-real-field-p
    (p13b4-r-carrier ctx)
    (p13b4-r-add ctx)
    (p13b4-r-mul ctx)
    (p13b4-r-neg ctx)
    (p13b4-r-inv ctx)
    (p13b4-r-zero ctx)
    (p13b4-r-one ctx)
    (p13b4-r-lt ctx))))

(defun p13b4-r-add-value (ctx x y)
  (p13b4-binary-value (p13b4-r-add ctx) x y))

(defun p13b4-r-mul-value (ctx x y)
  (p13b4-binary-value (p13b4-r-mul ctx) x y))

(defun p13b4-r-neg-value (ctx x)
  (p13b4-unary-value (p13b4-r-neg ctx) x))

(defun p13b4-r-inv-value (ctx x)
  (p13b4-unary-value (p13b4-r-inv ctx) x))

(defun p13b4-r-sub-value (ctx x y)
  (p13b4-r-add-value
   ctx x (p13b4-r-neg-value ctx y)))

(defun p13b4-r-div-value (ctx x y)
  (p13b4-r-mul-value
   ctx x (p13b4-r-inv-value ctx y)))

(defun p13b4-r-lt-p (ctx x y)
  (if (p13b4-binary-value
       (p13b4-r-lt ctx) x y)
      t nil))

(defun p13b4-r-le-p (ctx x y)
  (not (p13b4-r-lt-p ctx y x)))

(defun p13b4-r-abs-value (ctx x)
  (if (p13b4-r-lt-p
       ctx x (p13b4-r-zero ctx))
      (p13b4-r-neg-value ctx x)
    x))

(defun p13b4-positive-real-p (ctx x)
  (and
   (p13b4-member-p (p13b4-r-carrier ctx) x)
   (p13b4-r-lt-p
    ctx (p13b4-r-zero ctx) x)))

(defun p13b4-icc-member-p (ctx x)
  (and
   (p13b4-member-p (p13b4-r-carrier ctx) x)
   (p13b4-r-le-p ctx (p13b4-r-zero ctx) x)
   (p13b4-r-le-p ctx x (p13b4-r-one ctx))))

(defun p13b4-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p13b4-r-zero ctx)
    (p13b4-r-add-value
     ctx
     (p13b4-r-one ctx)
     (p13b4-nat-cast ctx (- n 1)))))

(defun p13b4-two (ctx)
  (p13b4-r-add-value
   ctx
   (p13b4-r-one ctx)
   (p13b4-r-one ctx)))

(defun p13b4-square (ctx x)
  (p13b4-r-mul-value ctx x x))

;; Relative epsilon-delta continuity on the closed unit interval.

(defun-sk p13b4-continuity-neighborhood-p
    (ctx function x epsilon radius)
  (forall (y)
    (implies
     (and
      (p13b4-icc-member-p ctx y)
      (p13b4-r-lt-p
       ctx
       (p13b4-r-abs-value
        ctx (p13b4-r-sub-value ctx y x))
       radius))
     (p13b4-r-lt-p
      ctx
      (p13b4-r-abs-value
       ctx
       (p13b4-r-sub-value
        ctx
        (p13b4-unary-value function y)
        (p13b4-unary-value function x)))
      epsilon))))

(defun-sk p13b4-continuity-radius-exists-p
    (ctx function x epsilon)
  (exists (radius)
    (and
     (p13b4-positive-real-p ctx radius)
     (p13b4-continuity-neighborhood-p
      ctx function x epsilon radius))))

(defun-sk p13b4-continuous-at-p
    (ctx function x)
  (forall (epsilon)
    (implies
     (p13b4-positive-real-p ctx epsilon)
     (p13b4-continuity-radius-exists-p
      ctx function x epsilon))))

(defun-sk p13b4-continuous-on-icc-p
    (ctx function)
  (forall (x)
    (implies
     (p13b4-icc-member-p ctx x)
     (p13b4-continuous-at-p
      ctx function x))))

(defun p13b4-admissible-function-p (ctx function)
  (and
   (tamep-functionp function)
   (p13b4-real-function-p
    (p13b4-r-carrier ctx) function)
   (p13b4-continuous-on-icc-p
    ctx function)))

;; Pointwise product and centered square.

(defun p13b4-product-function (ctx left right)
  (list
   'lambda '(x)
   (list
    'p13b4-r-mul-value
    (p13b4-quoted ctx)
    (p13b4-static-apply-term left '(x))
    (p13b4-static-apply-term right '(x)))))

(defun p13b4-centered-square-function
    (ctx function mean)
  (let ((centered
         (list
          'p13b4-r-sub-value
          (p13b4-quoted ctx)
          (p13b4-static-apply-term function '(x))
          (p13b4-quoted mean))))
    (list
     'lambda '(x)
     (list
      'p13b4-r-mul-value
      (p13b4-quoted ctx)
      centered
      centered))))

;; Uniform right-endpoint Riemann sums for the interval integral.

(defun p13b4-riemann-sum
    (ctx function subdivisions remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p13b4-r-zero ctx)
    (let* ((denominator
            (p13b4-nat-cast ctx subdivisions))
           (numerator
            (p13b4-nat-cast ctx remaining))
           (point
            (p13b4-r-div-value
             ctx numerator denominator)))
      (p13b4-r-add-value
       ctx
       (p13b4-unary-value function point)
       (p13b4-riemann-sum
        ctx function subdivisions
        (- remaining 1))))))

(defun p13b4-integral-approx
    (ctx function subdivisions)
  (if (posp subdivisions)
      (p13b4-r-div-value
       ctx
       (p13b4-riemann-sum
        ctx function subdivisions subdivisions)
       (p13b4-nat-cast ctx subdivisions))
    (p13b4-r-zero ctx)))

(defun-sk p13b4-integral-tail-p
    (ctx function value epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p13b4-r-lt-p
      ctx
      (p13b4-r-abs-value
       ctx
       (p13b4-r-sub-value
        ctx
        (p13b4-integral-approx
         ctx function subdivisions)
        value))
      epsilon))))

(defun-sk p13b4-integral-cutoff-exists-p
    (ctx function value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p13b4-integral-tail-p
      ctx function value epsilon cutoff))))

(defun-sk p13b4-integral-converges-to-p
    (ctx function value)
  (forall (epsilon)
    (implies
     (p13b4-positive-real-p ctx epsilon)
     (p13b4-integral-cutoff-exists-p
      ctx function value epsilon))))

(defun p13b4-integral-value-p
    (ctx function value)
  (and
   (p13b4-member-p (p13b4-r-carrier ctx) value)
   (p13b4-integral-converges-to-p
    ctx function value)))

;; Variance and maximum absolute value retain their defining witnesses.

(defun-sk p13b4-variance-value-p
    (ctx function value)
  (exists (mean)
    (and
     (p13b4-integral-value-p
      ctx function mean)
     (p13b4-integral-value-p
      ctx
      (p13b4-centered-square-function
       ctx function mean)
      value))))

(defun-sk p13b4-maximum-attained-p
    (ctx function value)
  (exists (x)
    (and
     (p13b4-icc-member-p ctx x)
     (equal
      (p13b4-r-abs-value
       ctx (p13b4-unary-value function x))
      value))))

(defun-sk p13b4-maximum-upper-bound-p
    (ctx function value)
  (forall (x)
    (implies
     (p13b4-icc-member-p ctx x)
     (p13b4-r-le-p
      ctx
      (p13b4-r-abs-value
       ctx (p13b4-unary-value function x))
      value))))

(defun p13b4-maximum-value-p
    (ctx function value)
  (and
   (p13b4-member-p (p13b4-r-carrier ctx) value)
   (p13b4-maximum-attained-p
    ctx function value)
   (p13b4-maximum-upper-bound-p
    ctx function value)))

(defun p13b4-bound-value
    (ctx variance-f variance-g maximum-f maximum-g)
  (p13b4-r-add-value
   ctx
   (p13b4-r-mul-value
    ctx
    (p13b4-r-mul-value
     ctx (p13b4-two ctx) variance-f)
    (p13b4-square ctx maximum-g))
   (p13b4-r-mul-value
    ctx
    (p13b4-r-mul-value
     ctx (p13b4-two ctx) variance-g)
    (p13b4-square ctx maximum-f))))

(defun-sk p13b4-inequality-values-exist-p
    (ctx f g)
  (exists
   (variance-product variance-f variance-g maximum-f maximum-g)
   (and
    (p13b4-variance-value-p
     ctx
     (p13b4-product-function ctx f g)
     variance-product)
    (p13b4-variance-value-p
     ctx f variance-f)
    (p13b4-variance-value-p
     ctx g variance-g)
    (p13b4-maximum-value-p
     ctx f maximum-f)
    (p13b4-maximum-value-p
     ctx g maximum-g)
    (p13b4-r-le-p
     ctx
     variance-product
     (p13b4-bound-value
      ctx variance-f variance-g maximum-f maximum-g)))))

(defun-sk putnambench-putnam-2013-b4-statement (ctx)
  (forall (f g)
    (implies
     (and
      (p13b4-context-p ctx)
      (p13b4-admissible-function-p ctx f)
      (p13b4-admissible-function-p ctx g))
     (p13b4-inequality-values-exist-p
      ctx f g))))

(value-triple :itpeval-statement-checked)
:q
