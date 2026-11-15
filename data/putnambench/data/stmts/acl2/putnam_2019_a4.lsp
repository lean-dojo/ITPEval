;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_a4:
;; a nonzero continuous real-valued function on real three-space has zero
;; surface integral over every sphere of radius one, so the answer is no.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar context is a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. Sine and cosine are fixed by their
;; Taylor-series limits, and PI is their usual least positive sine zero.
;; APPLY$ function objects retain the internally quantified arbitrary
;; real-valued function. The sphere integral is the unbounded limit of the
;; standard spherical-coordinate Riemann sums, including the sine Jacobian;
;; for continuous functions this is exactly integration against two-
;; dimensional Hausdorff measure on the unit sphere.

(defun p19a4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p19a4-unary-value (operation x)
  (apply$ operation (list x)))

(defun p19a4-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p19a4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p19a4-member-p carrier x))))

(defun-sk p19a4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p19a4-member-p carrier x)
      (p19a4-member-p carrier y)
      (p19a4-member-p carrier z))
     (and
      (p19a4-member-p
       carrier (p19a4-binary-value add x y))
      (p19a4-member-p
       carrier (p19a4-binary-value multiply x y))
      (p19a4-member-p
       carrier (p19a4-unary-value negate x))
      (p19a4-member-p
       carrier (p19a4-unary-value inverse x))
      (equal
       (p19a4-binary-value
        add (p19a4-binary-value add x y) z)
       (p19a4-binary-value
        add x (p19a4-binary-value add y z)))
      (equal
       (p19a4-binary-value add x y)
       (p19a4-binary-value add y x))
      (equal (p19a4-binary-value add x zero) x)
      (equal
       (p19a4-binary-value
        add x (p19a4-unary-value negate x))
       zero)
      (equal
       (p19a4-binary-value
        multiply
        (p19a4-binary-value multiply x y)
        z)
       (p19a4-binary-value
        multiply
        x
        (p19a4-binary-value multiply y z)))
      (equal
       (p19a4-binary-value multiply x y)
       (p19a4-binary-value multiply y x))
      (equal
       (p19a4-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p19a4-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p19a4-binary-value
         multiply x (p19a4-unary-value inverse x))
        one))
      (equal
       (p19a4-binary-value
        multiply x (p19a4-binary-value add y z))
       (p19a4-binary-value
        add
        (p19a4-binary-value multiply x y)
        (p19a4-binary-value multiply x z)))))))

(defun-sk p19a4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p19a4-member-p carrier x)
      (p19a4-member-p carrier y)
      (p19a4-member-p carrier z))
     (and
      (not (p19a4-binary-value less x x))
      (or
       (equal x y)
       (p19a4-binary-value less x y)
       (p19a4-binary-value less y x))
      (implies
       (and
        (p19a4-binary-value less x y)
        (p19a4-binary-value less y z))
       (p19a4-binary-value less x z))
      (implies
       (p19a4-binary-value less x y)
       (p19a4-binary-value
        less
        (p19a4-binary-value add x z)
        (p19a4-binary-value add y z)))
      (implies
       (and
        (p19a4-binary-value less zero x)
        (p19a4-binary-value less zero y))
       (p19a4-binary-value
        less
        zero
        (p19a4-binary-value multiply x y)))))))

(defun-sk p19a4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p19a4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p19a4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p19a4-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p19a4-binary-value less bound x)))))

(defun-sk p19a4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p19a4-member-p carrier bound)
     (p19a4-upper-bound-p
      carrier less set bound))))

(defun-sk p19a4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p19a4-member-p carrier bound)
      (p19a4-upper-bound-p
       carrier less set bound))
     (not
      (p19a4-binary-value
       less bound supremum)))))

(defun p19a4-supremum-p
    (carrier less set supremum)
  (and
   (p19a4-member-p carrier supremum)
   (p19a4-upper-bound-p
    carrier less set supremum)
   (p19a4-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p19a4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p19a4-supremum-p
     carrier less set supremum)))

(defun-sk p19a4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p19a4-valid-set-p carrier set)
      (p19a4-set-nonempty-p carrier set)
      (p19a4-bounded-above-p carrier less set))
     (p19a4-has-supremum-p
      carrier less set))))

(defun p19a4-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p19a4-member-p carrier zero)
   (p19a4-member-p carrier one)
   (not (equal zero one))
   (p19a4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p19a4-order-laws-p
    carrier add multiply zero less)
   (p19a4-binary-value less zero one)
   (p19a4-dedekind-complete-p carrier less)))

;; Context projections and real arithmetic.

(defun p19a4-r-carrier (ctx) (nth 0 ctx))
(defun p19a4-r-zero (ctx) (nth 1 ctx))
(defun p19a4-r-one (ctx) (nth 2 ctx))
(defun p19a4-r-add (ctx) (nth 3 ctx))
(defun p19a4-r-mul (ctx) (nth 4 ctx))
(defun p19a4-r-neg (ctx) (nth 5 ctx))
(defun p19a4-r-inv (ctx) (nth 6 ctx))
(defun p19a4-r-lt (ctx) (nth 7 ctx))
(defun p19a4-r-sin (ctx) (nth 8 ctx))
(defun p19a4-r-cos (ctx) (nth 9 ctx))
(defun p19a4-r-pi (ctx) (nth 10 ctx))

(defun p19a4-r-add-value (ctx x y)
  (p19a4-binary-value (p19a4-r-add ctx) x y))

(defun p19a4-r-mul-value (ctx x y)
  (p19a4-binary-value (p19a4-r-mul ctx) x y))

(defun p19a4-r-neg-value (ctx x)
  (p19a4-unary-value (p19a4-r-neg ctx) x))

(defun p19a4-r-inv-value (ctx x)
  (p19a4-unary-value (p19a4-r-inv ctx) x))

(defun p19a4-r-sub-value (ctx x y)
  (p19a4-r-add-value
   ctx x (p19a4-r-neg-value ctx y)))

(defun p19a4-r-div-value (ctx x y)
  (p19a4-r-mul-value
   ctx x (p19a4-r-inv-value ctx y)))

(defun p19a4-r-lt-p (ctx x y)
  (if (p19a4-binary-value
       (p19a4-r-lt ctx) x y)
      t nil))

(defun p19a4-r-abs-value (ctx x)
  (if (p19a4-r-lt-p
       ctx x (p19a4-r-zero ctx))
      (p19a4-r-neg-value ctx x)
    x))

(defun p19a4-positive-real-p (ctx x)
  (and
   (p19a4-member-p (p19a4-r-carrier ctx) x)
   (p19a4-r-lt-p
    ctx (p19a4-r-zero ctx) x)))

(defun p19a4-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p19a4-r-zero ctx)
    (p19a4-r-add-value
     ctx
     (p19a4-r-one ctx)
     (p19a4-nat-cast ctx (- n 1)))))

(defun p19a4-nat-power (ctx x exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p19a4-r-one ctx)
    (p19a4-r-mul-value
     ctx x
     (p19a4-nat-power ctx x (- exponent 1)))))

(defun p19a4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (nfix n)
       (p19a4-factorial (- n 1)))))

;; Sine and cosine are characterized by convergence of their Maclaurin
;; series at every real argument.

(defun p19a4-trig-term (ctx x cosine-p k)
  (let* ((exponent
          (if cosine-p
              (* 2 (nfix k))
            (+ 1 (* 2 (nfix k)))))
         (numerator
          (p19a4-nat-power ctx x exponent))
         (denominator
          (p19a4-nat-cast
           ctx (p19a4-factorial exponent)))
         (unsigned
          (p19a4-r-div-value
           ctx numerator denominator)))
    (if (equal (mod (nfix k) 2) 0)
        unsigned
      (p19a4-r-neg-value ctx unsigned))))

(defun p19a4-trig-partial-sum
    (ctx x cosine-p terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p19a4-r-zero ctx)
    (p19a4-r-add-value
     ctx
     (p19a4-trig-term
      ctx x cosine-p (- terms 1))
     (p19a4-trig-partial-sum
      ctx x cosine-p (- terms 1)))))

(defun p19a4-trig-value (ctx x cosine-p)
  (p19a4-unary-value
   (if cosine-p
       (p19a4-r-cos ctx)
     (p19a4-r-sin ctx))
   x))

(defun-sk p19a4-trig-tail-p
    (ctx x cosine-p epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (p19a4-r-lt-p
      ctx
      (p19a4-r-abs-value
       ctx
       (p19a4-r-sub-value
        ctx
        (p19a4-trig-partial-sum
         ctx x cosine-p terms)
        (p19a4-trig-value
         ctx x cosine-p)))
      epsilon))))

(defun-sk p19a4-trig-cutoff-exists-p
    (ctx x cosine-p epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p19a4-trig-tail-p
      ctx x cosine-p epsilon cutoff))))

(defun-sk p19a4-trig-converges-p
    (ctx x cosine-p)
  (forall (epsilon)
    (implies
     (p19a4-positive-real-p ctx epsilon)
     (p19a4-trig-cutoff-exists-p
      ctx x cosine-p epsilon))))

(defun-sk p19a4-trig-laws-p (ctx)
  (forall (x)
    (implies
     (p19a4-member-p (p19a4-r-carrier ctx) x)
     (and
      (p19a4-member-p
       (p19a4-r-carrier ctx)
       (p19a4-trig-value ctx x nil))
      (p19a4-member-p
       (p19a4-r-carrier ctx)
       (p19a4-trig-value ctx x t))
      (p19a4-trig-converges-p ctx x nil)
      (p19a4-trig-converges-p ctx x t)))))

(defun-sk p19a4-sine-positive-before-p (ctx)
  (forall (x)
    (implies
     (and
      (p19a4-member-p (p19a4-r-carrier ctx) x)
      (p19a4-r-lt-p
       ctx (p19a4-r-zero ctx) x)
      (p19a4-r-lt-p
       ctx x (p19a4-r-pi ctx)))
     (p19a4-r-lt-p
      ctx
      (p19a4-r-zero ctx)
      (p19a4-trig-value ctx x nil)))))

(defun p19a4-pi-p (ctx)
  (and
   (p19a4-positive-real-p
    ctx (p19a4-r-pi ctx))
   (equal
    (p19a4-trig-value
     ctx (p19a4-r-pi ctx) nil)
    (p19a4-r-zero ctx))
   (p19a4-sine-positive-before-p ctx)))

(defun p19a4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 11)
   (tamep-functionp (p19a4-r-sin ctx))
   (tamep-functionp (p19a4-r-cos ctx))
   (p19a4-real-field-p
    (p19a4-r-carrier ctx)
    (p19a4-r-add ctx)
    (p19a4-r-mul ctx)
    (p19a4-r-neg ctx)
    (p19a4-r-inv ctx)
    (p19a4-r-zero ctx)
    (p19a4-r-one ctx)
    (p19a4-r-lt ctx))
   (p19a4-trig-laws-p ctx)
   (p19a4-pi-p ctx)))

;; Real three-space and continuous real-valued function objects.

(defun p19a4-r3-point-p (ctx point)
  (and
   (true-listp point)
   (equal (len point) 3)
   (p19a4-member-p
    (p19a4-r-carrier ctx) (nth 0 point))
   (p19a4-member-p
    (p19a4-r-carrier ctx) (nth 1 point))
   (p19a4-member-p
    (p19a4-r-carrier ctx) (nth 2 point))))

(defun p19a4-square (ctx x)
  (p19a4-r-mul-value ctx x x))

(defun p19a4-distance-squared (ctx left right)
  (p19a4-r-add-value
   ctx
   (p19a4-square
    ctx
    (p19a4-r-sub-value
     ctx (nth 0 left) (nth 0 right)))
   (p19a4-r-add-value
    ctx
    (p19a4-square
     ctx
     (p19a4-r-sub-value
      ctx (nth 1 left) (nth 1 right)))
    (p19a4-square
     ctx
     (p19a4-r-sub-value
      ctx (nth 2 left) (nth 2 right))))))

(defun-sk p19a4-real-function-p (ctx function)
  (forall (point)
    (implies
     (p19a4-r3-point-p ctx point)
     (p19a4-member-p
      (p19a4-r-carrier ctx)
      (p19a4-unary-value function point)))))

(defun-sk p19a4-continuity-neighborhood-p
    (ctx function point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (p19a4-r3-point-p ctx nearby)
      (p19a4-r-lt-p
       ctx
       (p19a4-distance-squared
        ctx nearby point)
       (p19a4-square ctx radius)))
     (p19a4-r-lt-p
      ctx
      (p19a4-r-abs-value
       ctx
       (p19a4-r-sub-value
        ctx
        (p19a4-unary-value function nearby)
        (p19a4-unary-value function point)))
      epsilon))))

(defun-sk p19a4-continuity-radius-exists-p
    (ctx function point epsilon)
  (exists (radius)
    (and
     (p19a4-positive-real-p ctx radius)
     (p19a4-continuity-neighborhood-p
      ctx function point epsilon radius))))

(defun-sk p19a4-continuous-at-p
    (ctx function point)
  (forall (epsilon)
    (implies
     (p19a4-positive-real-p ctx epsilon)
     (p19a4-continuity-radius-exists-p
      ctx function point epsilon))))

(defun-sk p19a4-continuous-p
    (ctx function)
  (forall (point)
    (implies
     (p19a4-r3-point-p ctx point)
     (p19a4-continuous-at-p
      ctx function point))))

;; Uniform spherical-coordinate sums for the radius-one surface integral.

(defun p19a4-two (ctx)
  (p19a4-r-add-value
   ctx (p19a4-r-one ctx) (p19a4-r-one ctx)))

(defun p19a4-grid-angle
    (ctx scale index subdivisions)
  (p19a4-r-div-value
   ctx
   (p19a4-r-mul-value
    ctx scale (p19a4-nat-cast ctx index))
   (p19a4-nat-cast ctx subdivisions)))

(defun p19a4-sphere-point
    (ctx center theta phi)
  (let* ((sin-theta
          (p19a4-trig-value ctx theta nil))
         (cos-theta
          (p19a4-trig-value ctx theta t))
         (sin-phi
          (p19a4-trig-value ctx phi nil))
         (cos-phi
          (p19a4-trig-value ctx phi t)))
    (list
     (p19a4-r-add-value
      ctx
      (nth 0 center)
      (p19a4-r-mul-value
       ctx sin-theta cos-phi))
     (p19a4-r-add-value
      ctx
      (nth 1 center)
      (p19a4-r-mul-value
       ctx sin-theta sin-phi))
     (p19a4-r-add-value
      ctx
      (nth 2 center)
      cos-theta))))

(defun p19a4-surface-summand
    (ctx function center subdivisions i j)
  (let* ((theta
          (p19a4-grid-angle
           ctx (p19a4-r-pi ctx)
           i subdivisions))
         (two-pi
          (p19a4-r-mul-value
           ctx (p19a4-two ctx) (p19a4-r-pi ctx)))
         (phi
          (p19a4-grid-angle
           ctx two-pi j subdivisions))
         (point
          (p19a4-sphere-point
           ctx center theta phi)))
    (p19a4-r-mul-value
     ctx
     (p19a4-unary-value function point)
     (p19a4-trig-value ctx theta nil))))

(defun p19a4-surface-inner-sum
    (ctx function center subdivisions i remaining-j)
  (declare (xargs :measure (nfix remaining-j)))
  (if (zp remaining-j)
      (p19a4-r-zero ctx)
    (p19a4-r-add-value
     ctx
     (p19a4-surface-summand
      ctx function center subdivisions
      i remaining-j)
     (p19a4-surface-inner-sum
      ctx function center subdivisions
      i (- remaining-j 1)))))

(defun p19a4-surface-double-sum
    (ctx function center subdivisions remaining-i)
  (declare (xargs :measure (nfix remaining-i)))
  (if (zp remaining-i)
      (p19a4-r-zero ctx)
    (p19a4-r-add-value
     ctx
     (p19a4-surface-inner-sum
      ctx function center subdivisions
      remaining-i subdivisions)
     (p19a4-surface-double-sum
      ctx function center subdivisions
      (- remaining-i 1)))))

(defun p19a4-surface-integral-approx
    (ctx function center subdivisions)
  (if (posp subdivisions)
      (let* ((denominator
              (p19a4-nat-cast ctx subdivisions))
             (delta-theta
              (p19a4-r-div-value
               ctx (p19a4-r-pi ctx) denominator))
             (delta-phi
              (p19a4-r-div-value
               ctx
               (p19a4-r-mul-value
                ctx
                (p19a4-two ctx)
                (p19a4-r-pi ctx))
               denominator)))
        (p19a4-r-mul-value
         ctx
         (p19a4-r-mul-value
          ctx delta-theta delta-phi)
         (p19a4-surface-double-sum
          ctx function center subdivisions
          subdivisions)))
    (p19a4-r-zero ctx)))

(defun-sk p19a4-zero-surface-integral-tail-p
    (ctx function center epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p19a4-r-lt-p
      ctx
      (p19a4-r-abs-value
       ctx
       (p19a4-surface-integral-approx
        ctx function center subdivisions))
      epsilon))))

(defun-sk p19a4-zero-surface-integral-cutoff-exists-p
    (ctx function center epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p19a4-zero-surface-integral-tail-p
      ctx function center epsilon cutoff))))

(defun-sk p19a4-zero-surface-integral-p
    (ctx function center)
  (forall (epsilon)
    (implies
     (p19a4-positive-real-p ctx epsilon)
     (p19a4-zero-surface-integral-cutoff-exists-p
      ctx function center epsilon))))

(defun-sk p19a4-all-unit-sphere-integrals-zero-p
    (ctx function)
  (forall (center)
    (implies
     (p19a4-r3-point-p ctx center)
     (p19a4-zero-surface-integral-p
      ctx function center))))

(defun-sk p19a4-function-nonzero-p
    (ctx function)
  (exists (point)
    (and
     (p19a4-r3-point-p ctx point)
     (not
      (equal
       (p19a4-unary-value function point)
       (p19a4-r-zero ctx))))))

(defun-sk p19a4-counterexample-exists-p (ctx)
  (exists (function)
    (and
     (tamep-functionp function)
     (p19a4-real-function-p ctx function)
     (p19a4-continuous-p ctx function)
     (p19a4-all-unit-sphere-integrals-zero-p
      ctx function)
     (p19a4-function-nonzero-p
      ctx function))))

(defun putnambench-putnam-2019-a4-statement (ctx)
  (implies
   (p19a4-context-p ctx)
   (p19a4-counterexample-exists-p ctx)))

(value-triple :itpeval-statement-checked)
:q
