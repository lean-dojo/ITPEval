;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_b3:
;; every twice continuously differentiable real function on the plane has,
;; for each d > r > 0, a radius-r disk centered distance d from the origin
;; on which the integral of y*h_x-x*h_y is zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers up to unique
;; ordered-field isomorphism. APPLY$ objects present arbitrary predicates and
;; real-valued functions. All field, function, differentiability, continuity,
;; and integration conditions used by the statement are explicit below.

(defun p21b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p21b3-unary-value (function x)
  (apply$ function (list x)))

(defun p21b3-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p21b3-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p21b3-member-p carrier x))))

(defun-sk p21b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p21b3-member-p carrier x)
      (p21b3-member-p carrier y)
      (p21b3-member-p carrier z))
     (and
      (p21b3-member-p
       carrier (p21b3-binary-value add x y))
      (p21b3-member-p
       carrier (p21b3-binary-value multiply x y))
      (p21b3-member-p
       carrier (p21b3-unary-value negate x))
      (p21b3-member-p
       carrier (p21b3-unary-value inverse x))
      (equal
       (p21b3-binary-value
        add (p21b3-binary-value add x y) z)
       (p21b3-binary-value
        add x (p21b3-binary-value add y z)))
      (equal
       (p21b3-binary-value add x y)
       (p21b3-binary-value add y x))
      (equal (p21b3-binary-value add x zero) x)
      (equal
       (p21b3-binary-value
        add x (p21b3-unary-value negate x))
       zero)
      (equal
       (p21b3-binary-value
        multiply
        (p21b3-binary-value multiply x y)
        z)
       (p21b3-binary-value
        multiply
        x
        (p21b3-binary-value multiply y z)))
      (equal
       (p21b3-binary-value multiply x y)
       (p21b3-binary-value multiply y x))
      (equal
       (p21b3-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p21b3-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p21b3-binary-value
         multiply x (p21b3-unary-value inverse x))
        one))
      (equal
       (p21b3-binary-value
        multiply x (p21b3-binary-value add y z))
       (p21b3-binary-value
        add
        (p21b3-binary-value multiply x y)
        (p21b3-binary-value multiply x z)))))))

(defun-sk p21b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p21b3-member-p carrier x)
      (p21b3-member-p carrier y)
      (p21b3-member-p carrier z))
     (and
      (not (p21b3-binary-value less x x))
      (or
       (equal x y)
       (p21b3-binary-value less x y)
       (p21b3-binary-value less y x))
      (implies
       (and
        (p21b3-binary-value less x y)
        (p21b3-binary-value less y z))
       (p21b3-binary-value less x z))
      (implies
       (p21b3-binary-value less x y)
       (p21b3-binary-value
        less
        (p21b3-binary-value add x z)
        (p21b3-binary-value add y z)))
      (implies
       (and
        (p21b3-binary-value less zero x)
        (p21b3-binary-value less zero y))
       (p21b3-binary-value
        less
        zero
        (p21b3-binary-value multiply x y)))))))

(defun-sk p21b3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p21b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p21b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p21b3-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p21b3-binary-value less bound x)))))

(defun-sk p21b3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p21b3-member-p carrier bound)
     (p21b3-upper-bound-p carrier less set bound))))

(defun-sk p21b3-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p21b3-member-p carrier bound)
      (p21b3-upper-bound-p carrier less set bound))
     (not
      (p21b3-binary-value less bound supremum)))))

(defun p21b3-supremum-p
    (carrier less set supremum)
  (and
   (p21b3-member-p carrier supremum)
   (p21b3-upper-bound-p carrier less set supremum)
   (p21b3-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p21b3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p21b3-supremum-p
     carrier less set supremum)))

(defun-sk p21b3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p21b3-valid-set-p carrier set)
      (p21b3-set-nonempty-p carrier set)
      (p21b3-bounded-above-p carrier less set))
     (p21b3-has-supremum-p carrier less set))))

(defun p21b3-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p21b3-member-p carrier zero)
   (p21b3-member-p carrier one)
   (not (equal zero one))
   (p21b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p21b3-order-laws-p
    carrier add multiply zero less)
   (p21b3-binary-value less zero one)
   (p21b3-dedekind-complete-p carrier less)))

;; The context slots are carrier, zero, one, addition, multiplication,
;; negation, inverse, and strict order.

(defun p21b3-r-carrier (ctx) (nth 0 ctx))
(defun p21b3-r-zero (ctx) (nth 1 ctx))
(defun p21b3-r-one (ctx) (nth 2 ctx))
(defun p21b3-r-add (ctx) (nth 3 ctx))
(defun p21b3-r-mul (ctx) (nth 4 ctx))
(defun p21b3-r-neg (ctx) (nth 5 ctx))
(defun p21b3-r-inv (ctx) (nth 6 ctx))
(defun p21b3-r-lt (ctx) (nth 7 ctx))

(defun p21b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p21b3-real-field-p
    (p21b3-r-carrier ctx)
    (p21b3-r-add ctx)
    (p21b3-r-mul ctx)
    (p21b3-r-neg ctx)
    (p21b3-r-inv ctx)
    (p21b3-r-zero ctx)
    (p21b3-r-one ctx)
    (p21b3-r-lt ctx))))

(defun p21b3-r-add-value (ctx x y)
  (p21b3-binary-value (p21b3-r-add ctx) x y))

(defun p21b3-r-mul-value (ctx x y)
  (p21b3-binary-value (p21b3-r-mul ctx) x y))

(defun p21b3-r-neg-value (ctx x)
  (p21b3-unary-value (p21b3-r-neg ctx) x))

(defun p21b3-r-inv-value (ctx x)
  (p21b3-unary-value (p21b3-r-inv ctx) x))

(defun p21b3-r-sub-value (ctx x y)
  (p21b3-r-add-value
   ctx x (p21b3-r-neg-value ctx y)))

(defun p21b3-r-div-value (ctx x y)
  (p21b3-r-mul-value
   ctx x (p21b3-r-inv-value ctx y)))

(defun p21b3-r-square (ctx x)
  (p21b3-r-mul-value ctx x x))

(defun p21b3-r-lt-p (ctx x y)
  (if (p21b3-binary-value
       (p21b3-r-lt ctx) x y)
      t nil))

(defun p21b3-r-abs-value (ctx x)
  (if (p21b3-r-lt-p
       ctx x (p21b3-r-zero ctx))
      (p21b3-r-neg-value ctx x)
    x))

(defun p21b3-positive-real-p (ctx x)
  (and
   (p21b3-member-p (p21b3-r-carrier ctx) x)
   (p21b3-r-lt-p
    ctx (p21b3-r-zero ctx) x)))

(defun p21b3-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p21b3-r-zero ctx)
    (p21b3-r-add-value
     ctx
     (p21b3-r-one ctx)
     (p21b3-nat-cast ctx (- n 1)))))

(defun p21b3-plane-point (x y)
  (cons x y))

(defun p21b3-plane-value (function x y)
  (p21b3-unary-value
   function (p21b3-plane-point x y)))

(defun-sk p21b3-plane-function-values-p
    (ctx function)
  (forall (x y)
    (implies
     (and
      (p21b3-member-p (p21b3-r-carrier ctx) x)
      (p21b3-member-p (p21b3-r-carrier ctx) y))
     (p21b3-member-p
      (p21b3-r-carrier ctx)
      (p21b3-plane-value function x y)))))

(defun p21b3-plane-function-p (ctx function)
  (and
   (tamep-functionp function)
   (p21b3-plane-function-values-p ctx function)))

;; Continuity uses the max-coordinate metric, which induces exactly the
;; Euclidean topology on the real plane.

(defun-sk p21b3-continuity-neighborhood-p
    (ctx function x y epsilon delta)
  (forall (u v)
    (implies
     (and
      (p21b3-member-p (p21b3-r-carrier ctx) u)
      (p21b3-member-p (p21b3-r-carrier ctx) v)
      (p21b3-r-lt-p
       ctx
       (p21b3-r-abs-value
        ctx (p21b3-r-sub-value ctx u x))
       delta)
      (p21b3-r-lt-p
       ctx
       (p21b3-r-abs-value
        ctx (p21b3-r-sub-value ctx v y))
       delta))
     (p21b3-r-lt-p
      ctx
      (p21b3-r-abs-value
       ctx
       (p21b3-r-sub-value
        ctx
        (p21b3-plane-value function u v)
        (p21b3-plane-value function x y)))
      epsilon))))

(defun-sk p21b3-continuity-radius-exists-p
    (ctx function x y epsilon)
  (exists (delta)
    (and
     (p21b3-positive-real-p ctx delta)
     (p21b3-continuity-neighborhood-p
      ctx function x y epsilon delta))))

(defun-sk p21b3-continuous-p
    (ctx function)
  (forall (x y epsilon)
    (implies
     (and
      (p21b3-member-p (p21b3-r-carrier ctx) x)
      (p21b3-member-p (p21b3-r-carrier ctx) y)
      (p21b3-positive-real-p ctx epsilon))
     (p21b3-continuity-radius-exists-p
      ctx function x y epsilon))))

;; The remainder definition below is equivalent to the usual one-variable
;; derivative limit in each coordinate.

(defun p21b3-shifted-value
    (ctx function x y increment x-direction-p)
  (if x-direction-p
      (p21b3-plane-value
       function
       (p21b3-r-add-value ctx x increment)
       y)
    (p21b3-plane-value
     function
     x
     (p21b3-r-add-value ctx y increment))))

(defun-sk p21b3-partial-neighborhood-p
    (ctx function derivative x y epsilon delta x-direction-p)
  (forall (increment)
    (implies
     (and
      (p21b3-member-p
       (p21b3-r-carrier ctx) increment)
      (p21b3-r-lt-p
       ctx
       (p21b3-r-zero ctx)
       (p21b3-r-abs-value ctx increment))
      (p21b3-r-lt-p
       ctx
       (p21b3-r-abs-value ctx increment)
       delta))
     (p21b3-r-lt-p
      ctx
      (p21b3-r-abs-value
       ctx
       (p21b3-r-sub-value
        ctx
        (p21b3-r-sub-value
         ctx
         (p21b3-shifted-value
          ctx function x y increment x-direction-p)
         (p21b3-plane-value function x y))
        (p21b3-r-mul-value
         ctx
         (p21b3-plane-value derivative x y)
         increment)))
      (p21b3-r-mul-value
       ctx epsilon
       (p21b3-r-abs-value ctx increment))))))

(defun-sk p21b3-partial-radius-exists-p
    (ctx function derivative x y epsilon x-direction-p)
  (exists (delta)
    (and
     (p21b3-positive-real-p ctx delta)
     (p21b3-partial-neighborhood-p
      ctx function derivative x y
      epsilon delta x-direction-p))))

(defun-sk p21b3-partial-values-p
    (ctx function derivative x-direction-p)
  (forall (x y epsilon)
    (implies
     (and
      (p21b3-member-p (p21b3-r-carrier ctx) x)
      (p21b3-member-p (p21b3-r-carrier ctx) y)
      (p21b3-positive-real-p ctx epsilon))
     (p21b3-partial-radius-exists-p
      ctx function derivative x y
      epsilon x-direction-p))))

(defun p21b3-partial-derivative-function-p
    (ctx function derivative x-direction-p)
  (and
   (p21b3-plane-function-p ctx function)
   (p21b3-plane-function-p ctx derivative)
   (p21b3-partial-values-p
    ctx function derivative x-direction-p)))

;; The package contains h_x, h_y, h_xx, h_xy, h_yx, and h_yy.

(defun p21b3-hx (derivatives) (nth 0 derivatives))
(defun p21b3-hy (derivatives) (nth 1 derivatives))
(defun p21b3-hxx (derivatives) (nth 2 derivatives))
(defun p21b3-hxy (derivatives) (nth 3 derivatives))
(defun p21b3-hyx (derivatives) (nth 4 derivatives))
(defun p21b3-hyy (derivatives) (nth 5 derivatives))

(defun p21b3-c2-derivative-package-p
    (ctx function derivatives)
  (and
   (true-listp derivatives)
   (equal (len derivatives) 6)
   (p21b3-plane-function-p ctx function)
   (p21b3-continuous-p ctx function)
   (p21b3-continuous-p ctx (p21b3-hx derivatives))
   (p21b3-continuous-p ctx (p21b3-hy derivatives))
   (p21b3-continuous-p ctx (p21b3-hxx derivatives))
   (p21b3-continuous-p ctx (p21b3-hxy derivatives))
   (p21b3-continuous-p ctx (p21b3-hyx derivatives))
   (p21b3-continuous-p ctx (p21b3-hyy derivatives))
   (p21b3-partial-derivative-function-p
    ctx function (p21b3-hx derivatives) t)
   (p21b3-partial-derivative-function-p
    ctx function (p21b3-hy derivatives) nil)
   (p21b3-partial-derivative-function-p
    ctx (p21b3-hx derivatives) (p21b3-hxx derivatives) t)
   (p21b3-partial-derivative-function-p
    ctx (p21b3-hx derivatives) (p21b3-hxy derivatives) nil)
   (p21b3-partial-derivative-function-p
    ctx (p21b3-hy derivatives) (p21b3-hyx derivatives) t)
   (p21b3-partial-derivative-function-p
    ctx (p21b3-hy derivatives) (p21b3-hyy derivatives) nil)))

(defun-sk p21b3-c2-function-p (ctx function)
  (exists (derivatives)
    (p21b3-c2-derivative-package-p
     ctx function derivatives)))

;; Partial derivatives are unique. This conservative choice keeps their
;; witnesses internal to the C^2 predicate.

(defchoose p21b3-chosen-derivatives
    (derivatives)
    (ctx function)
  (p21b3-c2-derivative-package-p
   ctx function derivatives))

(defun p21b3-rho-value (ctx function x y)
  (let ((derivatives
         (p21b3-chosen-derivatives ctx function)))
    (p21b3-r-sub-value
     ctx
     (p21b3-r-mul-value
      ctx y
      (p21b3-plane-value
       (p21b3-hx derivatives) x y))
     (p21b3-r-mul-value
      ctx x
      (p21b3-plane-value
       (p21b3-hy derivatives) x y)))))

;; Uniform square-grid Riemann sums converge to the integral over the open
;; disk: the indicator's only discontinuities lie on the boundary circle,
;; which has area zero. The limit is unbounded in the subdivision count.

(defun p21b3-grid-step (ctx radius subdivisions)
  (p21b3-r-div-value
   ctx
   (p21b3-r-add-value ctx radius radius)
   (p21b3-nat-cast ctx subdivisions)))

(defun p21b3-grid-coordinate
    (ctx center radius subdivisions index)
  (p21b3-r-add-value
   ctx
   (p21b3-r-sub-value ctx center radius)
   (p21b3-r-mul-value
    ctx
    (p21b3-nat-cast ctx index)
    (p21b3-grid-step ctx radius subdivisions))))

(defun p21b3-in-open-disk-p
    (ctx x y center-x center-y radius)
  (p21b3-r-lt-p
   ctx
   (p21b3-r-add-value
    ctx
    (p21b3-r-square
     ctx (p21b3-r-sub-value ctx x center-x))
    (p21b3-r-square
     ctx (p21b3-r-sub-value ctx y center-y)))
   (p21b3-r-square ctx radius)))

(defun p21b3-grid-row-sum
    (ctx function center-x center-y radius
     subdivisions x-index y-index)
  (declare (xargs :measure (nfix y-index)))
  (if (zp y-index)
      (p21b3-r-zero ctx)
    (let ((x
           (p21b3-grid-coordinate
            ctx center-x radius subdivisions x-index))
          (y
           (p21b3-grid-coordinate
            ctx center-y radius subdivisions y-index)))
      (p21b3-r-add-value
       ctx
       (if (p21b3-in-open-disk-p
            ctx x y center-x center-y radius)
           (p21b3-rho-value ctx function x y)
         (p21b3-r-zero ctx))
       (p21b3-grid-row-sum
        ctx function center-x center-y radius
        subdivisions x-index (- y-index 1))))))

(defun p21b3-grid-sum
    (ctx function center-x center-y radius
     subdivisions x-index)
  (declare (xargs :measure (nfix x-index)))
  (if (zp x-index)
      (p21b3-r-zero ctx)
    (p21b3-r-add-value
     ctx
     (p21b3-grid-row-sum
      ctx function center-x center-y radius
      subdivisions x-index subdivisions)
     (p21b3-grid-sum
      ctx function center-x center-y radius
      subdivisions (- x-index 1)))))

(defun p21b3-disk-integral-approx
    (ctx function center-x center-y radius subdivisions)
  (if (posp subdivisions)
      (let ((step
             (p21b3-grid-step
              ctx radius subdivisions)))
        (p21b3-r-mul-value
         ctx
         (p21b3-grid-sum
          ctx function center-x center-y radius
          subdivisions subdivisions)
         (p21b3-r-square ctx step)))
    (p21b3-r-zero ctx)))

(defun-sk p21b3-integral-tail-p
    (ctx function center-x center-y radius
     value epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p21b3-r-lt-p
      ctx
      (p21b3-r-abs-value
       ctx
       (p21b3-r-sub-value
        ctx
        (p21b3-disk-integral-approx
         ctx function center-x center-y
         radius subdivisions)
        value))
      epsilon))))

(defun-sk p21b3-integral-cutoff-exists-p
    (ctx function center-x center-y radius value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p21b3-integral-tail-p
      ctx function center-x center-y radius
      value epsilon cutoff))))

(defun-sk p21b3-disk-integral-value-p
    (ctx function center-x center-y radius value)
  (forall (epsilon)
    (implies
     (p21b3-positive-real-p ctx epsilon)
     (p21b3-integral-cutoff-exists-p
      ctx function center-x center-y radius
      value epsilon))))

;; Since d is positive, cx^2+cy^2=d^2 is equivalent to Euclidean distance
;; from the center to the origin being exactly d.

(defun-sk p21b3-zero-center-exists-p
    (ctx function d radius)
  (exists (center-x center-y)
    (and
     (p21b3-member-p (p21b3-r-carrier ctx) center-x)
     (p21b3-member-p (p21b3-r-carrier ctx) center-y)
     (equal
      (p21b3-r-add-value
       ctx
       (p21b3-r-square ctx center-x)
       (p21b3-r-square ctx center-y))
      (p21b3-r-square ctx d))
     (p21b3-disk-integral-value-p
      ctx function center-x center-y radius
      (p21b3-r-zero ctx)))))

(defun-sk p21b3-source-proposition-p (ctx)
  (forall (function d radius)
    (implies
     (and
      (p21b3-c2-function-p ctx function)
      (p21b3-positive-real-p ctx d)
      (p21b3-positive-real-p ctx radius)
      (p21b3-r-lt-p ctx radius d))
     (p21b3-zero-center-exists-p
      ctx function d radius))))

;; The PutnamBench solution annotation is True, so the source biconditional
;; reduces to the proposition itself.

(defun putnambench-putnam-2021-b3-statement (ctx)
  (implies
   (p21b3-context-p ctx)
   (p21b3-source-proposition-p ctx)))

(value-triple :itpeval-statement-checked)
:q
