;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_b5:
;; the maximum of integral_0^1 x^2*f(x) dx minus integral_0^1 x*f(x)^2 dx
;; over continuous real functions is 1/16. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. APPLY$ objects represent sets and
;; arbitrary real functions, while DEFUN-SK keeps the maximizing function,
;; integral values, and universal function quantifier internal. For continuous
;; functions on [0,1], the unbounded uniform Riemann-sum limits below equal the
;; source interval integrals, so no finite quadrature or rational restriction
;; is introduced.

(defun p06b5-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p06b5-unary-value (operation x)
  (apply$ operation (list x)))

(defun p06b5-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p06b5-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p06b5-member-p carrier x))))

(defun-sk p06b5-real-function-p (carrier function)
  (forall (x)
    (implies
     (p06b5-member-p carrier x)
     (p06b5-member-p
      carrier
      (p06b5-unary-value function x)))))

(defun-sk p06b5-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p06b5-member-p carrier x)
      (p06b5-member-p carrier y)
      (p06b5-member-p carrier z))
     (and
      (p06b5-member-p
       carrier (p06b5-binary-value add x y))
      (p06b5-member-p
       carrier (p06b5-binary-value multiply x y))
      (p06b5-member-p
       carrier (p06b5-unary-value negate x))
      (p06b5-member-p
       carrier (p06b5-unary-value inverse x))
      (equal
       (p06b5-binary-value
        add (p06b5-binary-value add x y) z)
       (p06b5-binary-value
        add x (p06b5-binary-value add y z)))
      (equal
       (p06b5-binary-value add x y)
       (p06b5-binary-value add y x))
      (equal (p06b5-binary-value add x zero) x)
      (equal
       (p06b5-binary-value
        add x (p06b5-unary-value negate x))
       zero)
      (equal
       (p06b5-binary-value
        multiply
        (p06b5-binary-value multiply x y)
        z)
       (p06b5-binary-value
        multiply
        x
        (p06b5-binary-value multiply y z)))
      (equal
       (p06b5-binary-value multiply x y)
       (p06b5-binary-value multiply y x))
      (equal
       (p06b5-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p06b5-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p06b5-binary-value
         multiply x (p06b5-unary-value inverse x))
        one))
      (equal
       (p06b5-binary-value
        multiply x (p06b5-binary-value add y z))
       (p06b5-binary-value
        add
        (p06b5-binary-value multiply x y)
        (p06b5-binary-value multiply x z)))))))

(defun-sk p06b5-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p06b5-member-p carrier x)
      (p06b5-member-p carrier y)
      (p06b5-member-p carrier z))
     (and
      (not (p06b5-binary-value less x x))
      (or
       (equal x y)
       (p06b5-binary-value less x y)
       (p06b5-binary-value less y x))
      (implies
       (and
        (p06b5-binary-value less x y)
        (p06b5-binary-value less y z))
       (p06b5-binary-value less x z))
      (implies
       (p06b5-binary-value less x y)
       (p06b5-binary-value
        less
        (p06b5-binary-value add x z)
        (p06b5-binary-value add y z)))
      (implies
       (and
        (p06b5-binary-value less zero x)
        (p06b5-binary-value less zero y))
       (p06b5-binary-value
        less
        zero
        (p06b5-binary-value multiply x y)))))))

(defun-sk p06b5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p06b5-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p06b5-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p06b5-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p06b5-binary-value less bound x)))))

(defun-sk p06b5-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p06b5-member-p carrier bound)
     (p06b5-upper-bound-p
      carrier less set bound))))

(defun-sk p06b5-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p06b5-member-p carrier bound)
      (p06b5-upper-bound-p
       carrier less set bound))
     (not
      (p06b5-binary-value
       less bound supremum)))))

(defun p06b5-supremum-p
    (carrier less set supremum)
  (and
   (p06b5-member-p carrier supremum)
   (p06b5-upper-bound-p
    carrier less set supremum)
   (p06b5-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p06b5-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p06b5-supremum-p
     carrier less set supremum)))

(defun-sk p06b5-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p06b5-valid-set-p carrier set)
      (p06b5-set-nonempty-p carrier set)
      (p06b5-bounded-above-p carrier less set))
     (p06b5-has-supremum-p
      carrier less set))))

(defun p06b5-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p06b5-member-p carrier zero)
   (p06b5-member-p carrier one)
   (not (equal zero one))
   (p06b5-field-laws-p
    carrier add multiply negate inverse zero one)
   (p06b5-order-laws-p
    carrier add multiply zero less)
   (p06b5-binary-value less zero one)
   (p06b5-dedekind-complete-p carrier less)))

;; Real-field context and arithmetic.

(defun p06b5-r-carrier (ctx) (nth 0 ctx))
(defun p06b5-r-zero (ctx) (nth 1 ctx))
(defun p06b5-r-one (ctx) (nth 2 ctx))
(defun p06b5-r-add (ctx) (nth 3 ctx))
(defun p06b5-r-mul (ctx) (nth 4 ctx))
(defun p06b5-r-neg (ctx) (nth 5 ctx))
(defun p06b5-r-inv (ctx) (nth 6 ctx))
(defun p06b5-r-lt (ctx) (nth 7 ctx))

(defun p06b5-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p06b5-real-field-p
    (p06b5-r-carrier ctx)
    (p06b5-r-add ctx)
    (p06b5-r-mul ctx)
    (p06b5-r-neg ctx)
    (p06b5-r-inv ctx)
    (p06b5-r-zero ctx)
    (p06b5-r-one ctx)
    (p06b5-r-lt ctx))))

(defun p06b5-r-add-value (ctx x y)
  (p06b5-binary-value (p06b5-r-add ctx) x y))

(defun p06b5-r-mul-value (ctx x y)
  (p06b5-binary-value (p06b5-r-mul ctx) x y))

(defun p06b5-r-neg-value (ctx x)
  (p06b5-unary-value (p06b5-r-neg ctx) x))

(defun p06b5-r-inv-value (ctx x)
  (p06b5-unary-value (p06b5-r-inv ctx) x))

(defun p06b5-r-sub-value (ctx x y)
  (p06b5-r-add-value
   ctx x (p06b5-r-neg-value ctx y)))

(defun p06b5-r-div-value (ctx x y)
  (p06b5-r-mul-value
   ctx x (p06b5-r-inv-value ctx y)))

(defun p06b5-r-lt-p (ctx x y)
  (if (p06b5-binary-value
       (p06b5-r-lt ctx) x y)
      t nil))

(defun p06b5-r-le-p (ctx x y)
  (not (p06b5-r-lt-p ctx y x)))

(defun p06b5-r-abs-value (ctx x)
  (if (p06b5-r-lt-p
       ctx x (p06b5-r-zero ctx))
      (p06b5-r-neg-value ctx x)
    x))

(defun p06b5-positive-real-p (ctx x)
  (and
   (p06b5-member-p (p06b5-r-carrier ctx) x)
   (p06b5-r-lt-p
    ctx (p06b5-r-zero ctx) x)))

(defun p06b5-icc-member-p (ctx x)
  (and
   (p06b5-member-p (p06b5-r-carrier ctx) x)
   (p06b5-r-le-p ctx (p06b5-r-zero ctx) x)
   (p06b5-r-le-p ctx x (p06b5-r-one ctx))))

(defun p06b5-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p06b5-r-zero ctx)
    (p06b5-r-add-value
     ctx
     (p06b5-r-one ctx)
     (p06b5-nat-cast ctx (- n 1)))))

(defun p06b5-solution (ctx)
  (p06b5-r-div-value
   ctx
   (p06b5-r-one ctx)
   (p06b5-nat-cast ctx 16)))

;; Relative epsilon-delta continuity on the closed unit interval.

(defun-sk p06b5-continuity-neighborhood-p
    (ctx function x epsilon radius)
  (forall (y)
    (implies
     (and
      (p06b5-icc-member-p ctx y)
      (p06b5-r-lt-p
       ctx
       (p06b5-r-abs-value
        ctx (p06b5-r-sub-value ctx y x))
       radius))
     (p06b5-r-lt-p
      ctx
      (p06b5-r-abs-value
       ctx
       (p06b5-r-sub-value
        ctx
        (p06b5-unary-value function y)
        (p06b5-unary-value function x)))
      epsilon))))

(defun-sk p06b5-continuity-radius-exists-p
    (ctx function x epsilon)
  (exists (radius)
    (and
     (p06b5-positive-real-p ctx radius)
     (p06b5-continuity-neighborhood-p
      ctx function x epsilon radius))))

(defun-sk p06b5-continuous-at-p
    (ctx function x)
  (forall (epsilon)
    (implies
     (p06b5-positive-real-p ctx epsilon)
     (p06b5-continuity-radius-exists-p
      ctx function x epsilon))))

(defun-sk p06b5-continuous-on-icc-p
    (ctx function)
  (forall (x)
    (implies
     (p06b5-icc-member-p ctx x)
     (p06b5-continuous-at-p
      ctx function x))))

(defun p06b5-admissible-function-p (ctx function)
  (and
   (tamep-functionp function)
   (p06b5-real-function-p
    (p06b5-r-carrier ctx) function)
   (p06b5-continuous-on-icc-p
    ctx function)))

;; Uniform right-endpoint Riemann sums for I(f) and J(f).

(defun p06b5-integrand-value
    (ctx function j-integral-p x)
  (let ((fx (p06b5-unary-value function x)))
    (if j-integral-p
        (p06b5-r-mul-value
         ctx x (p06b5-r-mul-value ctx fx fx))
      (p06b5-r-mul-value
       ctx
       (p06b5-r-mul-value ctx x x)
       fx))))

(defun p06b5-riemann-sum
    (ctx function j-integral-p subdivisions remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p06b5-r-zero ctx)
    (let* ((denominator
            (p06b5-nat-cast ctx subdivisions))
           (numerator
            (p06b5-nat-cast ctx remaining))
           (point
            (p06b5-r-div-value
             ctx numerator denominator)))
      (p06b5-r-add-value
       ctx
       (p06b5-integrand-value
        ctx function j-integral-p point)
       (p06b5-riemann-sum
        ctx function j-integral-p subdivisions
        (- remaining 1))))))

(defun p06b5-integral-approx
    (ctx function j-integral-p subdivisions)
  (if (posp subdivisions)
      (p06b5-r-div-value
       ctx
       (p06b5-riemann-sum
        ctx function j-integral-p
        subdivisions subdivisions)
       (p06b5-nat-cast ctx subdivisions))
    (p06b5-r-zero ctx)))

(defun-sk p06b5-integral-tail-p
    (ctx function j-integral-p value epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p06b5-r-lt-p
      ctx
      (p06b5-r-abs-value
       ctx
       (p06b5-r-sub-value
        ctx
        (p06b5-integral-approx
         ctx function j-integral-p subdivisions)
        value))
      epsilon))))

(defun-sk p06b5-integral-cutoff-exists-p
    (ctx function j-integral-p value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p06b5-integral-tail-p
      ctx function j-integral-p value epsilon cutoff))))

(defun-sk p06b5-integral-converges-to-p
    (ctx function j-integral-p value)
  (forall (epsilon)
    (implies
     (p06b5-positive-real-p ctx epsilon)
     (p06b5-integral-cutoff-exists-p
      ctx function j-integral-p value epsilon))))

(defun p06b5-integral-value-p
    (ctx function j-integral-p value)
  (and
   (p06b5-member-p (p06b5-r-carrier ctx) value)
   (p06b5-integral-converges-to-p
    ctx function j-integral-p value)))

(defun-sk p06b5-maximum-attained-p (ctx)
  (exists (function integral-i integral-j)
    (and
     (p06b5-admissible-function-p ctx function)
     (p06b5-integral-value-p
      ctx function nil integral-i)
     (p06b5-integral-value-p
      ctx function t integral-j)
     (equal
      (p06b5-r-sub-value
       ctx integral-i integral-j)
      (p06b5-solution ctx)))))

(defun-sk p06b5-function-objective-bounded-p
    (ctx function)
  (exists (integral-i integral-j)
    (and
     (p06b5-integral-value-p
      ctx function nil integral-i)
     (p06b5-integral-value-p
      ctx function t integral-j)
     (p06b5-r-le-p
      ctx
      (p06b5-r-sub-value
       ctx integral-i integral-j)
      (p06b5-solution ctx)))))

(defun-sk p06b5-all-objectives-bounded-p (ctx)
  (forall (function)
    (implies
     (p06b5-admissible-function-p ctx function)
     (p06b5-function-objective-bounded-p
      ctx function))))

(defun putnambench-putnam-2006-b5-statement (ctx)
  (implies
   (p06b5-context-p ctx)
   (and
    (p06b5-maximum-attained-p ctx)
    (p06b5-all-objectives-bounded-p ctx))))

(value-triple :itpeval-statement-checked)
:q
