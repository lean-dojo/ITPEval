;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_b4:
;; a continuously differentiable real function on [0,1] with f(0)=0 and
;; 0<f'(x)<=1 satisfies (integral f)^2 >= integral(f^3), with the identity
;; function attaining equality. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. APPLY$ objects represent sets and
;; functions. Differentiability and derivative continuity are expanded into
;; epsilon-delta predicates. For continuous functions on [0,1], the unbounded
;; right-endpoint Riemann-sum limit below is exactly the source Lebesgue
;; integral, so no finite quadrature or rational-domain restriction is used.

(defun p73b4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p73b4-unary-value (operation x)
  (apply$ operation (list x)))

(defun p73b4-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p73b4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p73b4-member-p carrier x))))

(defun-sk p73b4-real-function-p (carrier function)
  (forall (x)
    (implies
     (p73b4-member-p carrier x)
     (p73b4-member-p
      carrier
      (p73b4-unary-value function x)))))

(defun-sk p73b4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p73b4-member-p carrier x)
      (p73b4-member-p carrier y)
      (p73b4-member-p carrier z))
     (and
      (p73b4-member-p
       carrier (p73b4-binary-value add x y))
      (p73b4-member-p
       carrier (p73b4-binary-value multiply x y))
      (p73b4-member-p
       carrier (p73b4-unary-value negate x))
      (implies
       (not (equal x zero))
       (p73b4-member-p
        carrier (p73b4-unary-value inverse x)))
      (equal
       (p73b4-binary-value
        add (p73b4-binary-value add x y) z)
       (p73b4-binary-value
        add x (p73b4-binary-value add y z)))
      (equal
       (p73b4-binary-value add x y)
       (p73b4-binary-value add y x))
      (equal (p73b4-binary-value add x zero) x)
      (equal
       (p73b4-binary-value
        add x (p73b4-unary-value negate x))
       zero)
      (equal
       (p73b4-binary-value
        multiply
        (p73b4-binary-value multiply x y)
        z)
       (p73b4-binary-value
        multiply
        x
        (p73b4-binary-value multiply y z)))
      (equal
       (p73b4-binary-value multiply x y)
       (p73b4-binary-value multiply y x))
      (equal
       (p73b4-binary-value multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (p73b4-binary-value
         multiply x (p73b4-unary-value inverse x))
        one))
      (equal
       (p73b4-binary-value
        multiply x (p73b4-binary-value add y z))
       (p73b4-binary-value
        add
        (p73b4-binary-value multiply x y)
        (p73b4-binary-value multiply x z)))))))

(defun-sk p73b4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p73b4-member-p carrier x)
      (p73b4-member-p carrier y)
      (p73b4-member-p carrier z))
     (and
      (not (p73b4-binary-value less x x))
      (or
       (equal x y)
       (p73b4-binary-value less x y)
       (p73b4-binary-value less y x))
      (implies
       (and
        (p73b4-binary-value less x y)
        (p73b4-binary-value less y z))
       (p73b4-binary-value less x z))
      (implies
       (p73b4-binary-value less x y)
       (p73b4-binary-value
        less
        (p73b4-binary-value add x z)
        (p73b4-binary-value add y z)))
      (implies
       (and
        (p73b4-binary-value less zero x)
        (p73b4-binary-value less zero y))
       (p73b4-binary-value
        less
        zero
        (p73b4-binary-value multiply x y)))))))

(defun-sk p73b4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p73b4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p73b4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p73b4-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p73b4-binary-value less bound x)))))

(defun-sk p73b4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p73b4-member-p carrier bound)
     (p73b4-upper-bound-p
      carrier less set bound))))

(defun-sk p73b4-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (p73b4-member-p carrier supremum)
     (p73b4-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (p73b4-member-p carrier bound)
       (p73b4-upper-bound-p
        carrier less set bound))
      (not
       (p73b4-binary-value
        less bound supremum))))))

(defun-sk p73b4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p73b4-supremum-p
     carrier less set supremum)))

(defun-sk p73b4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p73b4-valid-set-p carrier set)
      (p73b4-set-nonempty-p carrier set)
      (p73b4-bounded-above-p carrier less set))
     (p73b4-has-supremum-p
      carrier less set))))

(defun p73b4-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p73b4-member-p carrier zero)
   (p73b4-member-p carrier one)
   (not (equal zero one))
   (p73b4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p73b4-order-laws-p
    carrier add multiply zero less)
   (p73b4-binary-value less zero one)
   (p73b4-dedekind-complete-p carrier less)))

;; Real-field context and arithmetic.

(defun p73b4-r-carrier (ctx) (nth 0 ctx))
(defun p73b4-r-zero (ctx) (nth 1 ctx))
(defun p73b4-r-one (ctx) (nth 2 ctx))
(defun p73b4-r-add (ctx) (nth 3 ctx))
(defun p73b4-r-mul (ctx) (nth 4 ctx))
(defun p73b4-r-neg (ctx) (nth 5 ctx))
(defun p73b4-r-inv (ctx) (nth 6 ctx))
(defun p73b4-r-lt (ctx) (nth 7 ctx))

(defun p73b4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p73b4-real-field-p
    (p73b4-r-carrier ctx)
    (p73b4-r-add ctx)
    (p73b4-r-mul ctx)
    (p73b4-r-neg ctx)
    (p73b4-r-inv ctx)
    (p73b4-r-zero ctx)
    (p73b4-r-one ctx)
    (p73b4-r-lt ctx))))

(defun p73b4-r-add-value (ctx x y)
  (p73b4-binary-value (p73b4-r-add ctx) x y))

(defun p73b4-r-mul-value (ctx x y)
  (p73b4-binary-value (p73b4-r-mul ctx) x y))

(defun p73b4-r-neg-value (ctx x)
  (p73b4-unary-value (p73b4-r-neg ctx) x))

(defun p73b4-r-inv-value (ctx x)
  (p73b4-unary-value (p73b4-r-inv ctx) x))

(defun p73b4-r-sub-value (ctx x y)
  (p73b4-r-add-value
   ctx x (p73b4-r-neg-value ctx y)))

(defun p73b4-r-div-value (ctx x y)
  (p73b4-r-mul-value
   ctx x (p73b4-r-inv-value ctx y)))

(defun p73b4-r-lt-p (ctx x y)
  (if (p73b4-binary-value
       (p73b4-r-lt ctx) x y)
      t nil))

(defun p73b4-r-le-p (ctx x y)
  (not (p73b4-r-lt-p ctx y x)))

(defun p73b4-r-abs-value (ctx x)
  (if (p73b4-r-lt-p
       ctx x (p73b4-r-zero ctx))
      (p73b4-r-neg-value ctx x)
    x))

(defun p73b4-positive-real-p (ctx x)
  (and
   (p73b4-member-p (p73b4-r-carrier ctx) x)
   (p73b4-r-lt-p
    ctx (p73b4-r-zero ctx) x)))

(defun p73b4-icc-member-p (ctx x)
  (and
   (p73b4-member-p (p73b4-r-carrier ctx) x)
   (p73b4-r-le-p ctx (p73b4-r-zero ctx) x)
   (p73b4-r-le-p ctx x (p73b4-r-one ctx))))

;; Continuous differentiability on [0,1].

(defun-sk p73b4-continuity-neighborhood-p
    (ctx function x epsilon radius)
  (forall (y)
    (implies
     (and
      (p73b4-icc-member-p ctx y)
      (p73b4-r-lt-p
       ctx
       (p73b4-r-abs-value
        ctx (p73b4-r-sub-value ctx y x))
       radius))
     (p73b4-r-lt-p
      ctx
      (p73b4-r-abs-value
       ctx
       (p73b4-r-sub-value
        ctx
        (p73b4-unary-value function y)
        (p73b4-unary-value function x)))
      epsilon))))

(defun-sk p73b4-continuity-radius-exists-p
    (ctx function x epsilon)
  (exists (radius)
    (and
     (p73b4-positive-real-p ctx radius)
     (p73b4-continuity-neighborhood-p
      ctx function x epsilon radius))))

(defun-sk p73b4-continuous-at-p
    (ctx function x)
  (forall (epsilon)
    (implies
     (p73b4-positive-real-p ctx epsilon)
     (p73b4-continuity-radius-exists-p
      ctx function x epsilon))))

(defun-sk p73b4-continuous-on-icc-p
    (ctx function)
  (forall (x)
    (implies
     (p73b4-icc-member-p ctx x)
     (p73b4-continuous-at-p
      ctx function x))))

(defun p73b4-difference-quotient
    (ctx function x y)
  (p73b4-r-div-value
   ctx
   (p73b4-r-sub-value
    ctx
    (p73b4-unary-value function y)
    (p73b4-unary-value function x))
   (p73b4-r-sub-value ctx y x)))

(defun-sk p73b4-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p73b4-icc-member-p ctx y)
      (not (equal y x))
      (p73b4-r-lt-p
       ctx
       (p73b4-r-abs-value
        ctx (p73b4-r-sub-value ctx y x))
       radius))
     (p73b4-r-lt-p
      ctx
      (p73b4-r-abs-value
       ctx
       (p73b4-r-sub-value
        ctx
        (p73b4-difference-quotient
         ctx function x y)
        derivative))
      epsilon))))

(defun-sk p73b4-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p73b4-positive-real-p ctx radius)
     (p73b4-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p73b4-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p73b4-positive-real-p ctx epsilon)
     (p73b4-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p73b4-derivative-correct-on-icc-p
    (ctx function derivative-function)
  (forall (x)
    (implies
     (p73b4-icc-member-p ctx x)
     (p73b4-has-derivative-at-p
      ctx
      function
      (p73b4-unary-value derivative-function x)
      x))))

(defun-sk p73b4-derivative-bounds-p
    (ctx derivative-function)
  (forall (x)
    (implies
     (p73b4-icc-member-p ctx x)
     (and
      (p73b4-r-lt-p
       ctx
       (p73b4-r-zero ctx)
       (p73b4-unary-value derivative-function x))
      (p73b4-r-le-p
       ctx
       (p73b4-unary-value derivative-function x)
       (p73b4-r-one ctx))))))

(defun-sk p73b4-admissible-p (ctx function)
  (exists (derivative-function)
    (and
     (tamep-functionp derivative-function)
     (p73b4-real-function-p
      (p73b4-r-carrier ctx)
      derivative-function)
     (p73b4-continuous-on-icc-p
      ctx derivative-function)
     (p73b4-derivative-correct-on-icc-p
      ctx function derivative-function)
     (p73b4-derivative-bounds-p
      ctx derivative-function)
     (equal
      (p73b4-unary-value
       function (p73b4-r-zero ctx))
      (p73b4-r-zero ctx)))))

;; Riemann-sum presentation of the interval Lebesgue integrals.

(defun p73b4-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p73b4-r-zero ctx)
    (p73b4-r-add-value
     ctx
     (p73b4-r-one ctx)
     (p73b4-nat-cast ctx (- n 1)))))

(defun p73b4-integrand-value
    (ctx function cube-p x)
  (let ((value (p73b4-unary-value function x)))
    (if cube-p
        (p73b4-r-mul-value
         ctx
         value
         (p73b4-r-mul-value ctx value value))
      value)))

(defun p73b4-riemann-sum
    (ctx function cube-p subdivisions remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p73b4-r-zero ctx)
    (let* ((denominator
            (p73b4-nat-cast ctx subdivisions))
           (numerator
            (p73b4-nat-cast ctx remaining))
           (point
            (p73b4-r-div-value
             ctx numerator denominator)))
      (p73b4-r-add-value
       ctx
       (p73b4-integrand-value
        ctx function cube-p point)
       (p73b4-riemann-sum
        ctx function cube-p subdivisions
        (- remaining 1))))))

(defun p73b4-integral-approx
    (ctx function cube-p subdivisions)
  (if (posp subdivisions)
      (p73b4-r-div-value
       ctx
       (p73b4-riemann-sum
        ctx function cube-p subdivisions subdivisions)
       (p73b4-nat-cast ctx subdivisions))
    (p73b4-r-zero ctx)))

(defun-sk p73b4-integral-tail-p
    (ctx function cube-p value epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p73b4-r-lt-p
      ctx
      (p73b4-r-abs-value
       ctx
       (p73b4-r-sub-value
        ctx
        (p73b4-integral-approx
         ctx function cube-p subdivisions)
        value))
      epsilon))))

(defun-sk p73b4-integral-cutoff-exists-p
    (ctx function cube-p value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p73b4-integral-tail-p
      ctx function cube-p value epsilon cutoff))))

(defun-sk p73b4-integral-converges-to-p
    (ctx function cube-p value)
  (forall (epsilon)
    (implies
     (p73b4-positive-real-p ctx epsilon)
     (p73b4-integral-cutoff-exists-p
      ctx function cube-p value epsilon))))

(defun p73b4-integral-value-p
    (ctx function cube-p value)
  (and
   (p73b4-member-p (p73b4-r-carrier ctx) value)
   (p73b4-integral-converges-to-p
    ctx function cube-p value)))

(defun-sk p73b4-inequality-witnesses-exist-p
    (ctx function)
  (exists (integral-f integral-cube)
    (and
     (p73b4-integral-value-p
      ctx function nil integral-f)
     (p73b4-integral-value-p
      ctx function t integral-cube)
     (p73b4-r-le-p
      ctx
      integral-cube
      (p73b4-r-mul-value
       ctx integral-f integral-f)))))

;; The identity function is the requested equality case.

(defun p73b4-identity-function ()
  (list 'lambda '(x) 'x))

(defun-sk p73b4-identity-equality-witnesses-exist-p
    (ctx)
  (exists (integral-identity integral-cube)
    (and
     (p73b4-integral-value-p
      ctx
      (p73b4-identity-function)
      nil
      integral-identity)
     (p73b4-integral-value-p
      ctx
      (p73b4-identity-function)
      t
      integral-cube)
     (equal
      (p73b4-r-mul-value
       ctx integral-identity integral-identity)
      integral-cube))))

(defun putnambench-putnam-1973-b4-statement
    (ctx function)
  (implies
   (and
    (p73b4-context-p ctx)
    (tamep-functionp function)
    (p73b4-real-function-p
     (p73b4-r-carrier ctx) function)
    (p73b4-admissible-p ctx function))
   (and
    (p73b4-inequality-witnesses-exist-p
     ctx function)
    (tamep-functionp
     (p73b4-identity-function))
    (p73b4-real-function-p
     (p73b4-r-carrier ctx)
     (p73b4-identity-function))
    (p73b4-admissible-p
     ctx (p73b4-identity-function))
    (p73b4-identity-equality-witnesses-exist-p
     ctx))))

(value-triple :itpeval-statement-checked)
:q
