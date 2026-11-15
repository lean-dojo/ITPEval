;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_a6:
;; every continuous real-valued function on the plane whose integral over each
;; axis-aligned rectangle of area one is zero is identically zero. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. Tame APPLY$ objects represent
;; arbitrary real functions, and DEFUN-SK keeps the function, points,
;; continuity radii, rectangle endpoints, and integral cutoffs internally
;; quantified. The double integrals are exact limits of unbounded uniform
;; right-endpoint Riemann sums, which agree with the source integrals for
;; continuous functions on compact rectangles.

(defun p12a6-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p12a6-unary-value (operation x)
  (apply$ operation (list x)))

(defun p12a6-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun p12a6-function-value (function x y)
  (apply$ function (list x y)))

(defun-sk p12a6-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p12a6-member-p carrier x))))

(defun-sk p12a6-real-plane-function-p
    (carrier function)
  (forall (x y)
    (implies
     (and
      (p12a6-member-p carrier x)
      (p12a6-member-p carrier y))
     (p12a6-member-p
      carrier
      (p12a6-function-value function x y)))))

(defun-sk p12a6-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p12a6-member-p carrier x)
      (p12a6-member-p carrier y)
      (p12a6-member-p carrier z))
     (and
      (p12a6-member-p
       carrier (p12a6-binary-value add x y))
      (p12a6-member-p
       carrier (p12a6-binary-value multiply x y))
      (p12a6-member-p
       carrier (p12a6-unary-value negate x))
      (p12a6-member-p
       carrier (p12a6-unary-value inverse x))
      (equal
       (p12a6-binary-value
        add (p12a6-binary-value add x y) z)
       (p12a6-binary-value
        add x (p12a6-binary-value add y z)))
      (equal
       (p12a6-binary-value add x y)
       (p12a6-binary-value add y x))
      (equal (p12a6-binary-value add x zero) x)
      (equal
       (p12a6-binary-value
        add x (p12a6-unary-value negate x))
       zero)
      (equal
       (p12a6-binary-value
        multiply
        (p12a6-binary-value multiply x y)
        z)
       (p12a6-binary-value
        multiply
        x
        (p12a6-binary-value multiply y z)))
      (equal
       (p12a6-binary-value multiply x y)
       (p12a6-binary-value multiply y x))
      (equal
       (p12a6-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p12a6-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p12a6-binary-value
         multiply x (p12a6-unary-value inverse x))
        one))
      (equal
       (p12a6-binary-value
        multiply x (p12a6-binary-value add y z))
       (p12a6-binary-value
        add
        (p12a6-binary-value multiply x y)
        (p12a6-binary-value multiply x z)))))))

(defun-sk p12a6-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p12a6-member-p carrier x)
      (p12a6-member-p carrier y)
      (p12a6-member-p carrier z))
     (and
      (not (p12a6-binary-value less x x))
      (or
       (equal x y)
       (p12a6-binary-value less x y)
       (p12a6-binary-value less y x))
      (implies
       (and
        (p12a6-binary-value less x y)
        (p12a6-binary-value less y z))
       (p12a6-binary-value less x z))
      (implies
       (p12a6-binary-value less x y)
       (p12a6-binary-value
        less
        (p12a6-binary-value add x z)
        (p12a6-binary-value add y z)))
      (implies
       (and
        (p12a6-binary-value less zero x)
        (p12a6-binary-value less zero y))
       (p12a6-binary-value
        less
        zero
        (p12a6-binary-value multiply x y)))))))

(defun-sk p12a6-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p12a6-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p12a6-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p12a6-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p12a6-binary-value less bound x)))))

(defun-sk p12a6-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p12a6-member-p carrier bound)
     (p12a6-upper-bound-p
      carrier less set bound))))

(defun-sk p12a6-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p12a6-member-p carrier bound)
      (p12a6-upper-bound-p
       carrier less set bound))
     (not
      (p12a6-binary-value
       less bound supremum)))))

(defun p12a6-supremum-p
    (carrier less set supremum)
  (and
   (p12a6-member-p carrier supremum)
   (p12a6-upper-bound-p
    carrier less set supremum)
   (p12a6-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p12a6-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p12a6-supremum-p
     carrier less set supremum)))

(defun-sk p12a6-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p12a6-valid-set-p carrier set)
      (p12a6-set-nonempty-p carrier set)
      (p12a6-bounded-above-p carrier less set))
     (p12a6-has-supremum-p
      carrier less set))))

(defun p12a6-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p12a6-member-p carrier zero)
   (p12a6-member-p carrier one)
   (not (equal zero one))
   (p12a6-field-laws-p
    carrier add multiply negate inverse zero one)
   (p12a6-order-laws-p
    carrier add multiply zero less)
   (p12a6-binary-value less zero one)
   (p12a6-dedekind-complete-p carrier less)))

;; Real-field context and arithmetic.

(defun p12a6-r-carrier (ctx) (nth 0 ctx))
(defun p12a6-r-zero (ctx) (nth 1 ctx))
(defun p12a6-r-one (ctx) (nth 2 ctx))
(defun p12a6-r-add (ctx) (nth 3 ctx))
(defun p12a6-r-mul (ctx) (nth 4 ctx))
(defun p12a6-r-neg (ctx) (nth 5 ctx))
(defun p12a6-r-inv (ctx) (nth 6 ctx))
(defun p12a6-r-lt (ctx) (nth 7 ctx))

(defun p12a6-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p12a6-real-field-p
    (p12a6-r-carrier ctx)
    (p12a6-r-add ctx)
    (p12a6-r-mul ctx)
    (p12a6-r-neg ctx)
    (p12a6-r-inv ctx)
    (p12a6-r-zero ctx)
    (p12a6-r-one ctx)
    (p12a6-r-lt ctx))))

(defun p12a6-r-add-value (ctx x y)
  (p12a6-binary-value (p12a6-r-add ctx) x y))

(defun p12a6-r-mul-value (ctx x y)
  (p12a6-binary-value (p12a6-r-mul ctx) x y))

(defun p12a6-r-neg-value (ctx x)
  (p12a6-unary-value (p12a6-r-neg ctx) x))

(defun p12a6-r-inv-value (ctx x)
  (p12a6-unary-value (p12a6-r-inv ctx) x))

(defun p12a6-r-sub-value (ctx x y)
  (p12a6-r-add-value
   ctx x (p12a6-r-neg-value ctx y)))

(defun p12a6-r-div-value (ctx x y)
  (p12a6-r-mul-value
   ctx x (p12a6-r-inv-value ctx y)))

(defun p12a6-r-lt-p (ctx x y)
  (if (p12a6-binary-value
       (p12a6-r-lt ctx) x y)
      t nil))

(defun p12a6-r-abs-value (ctx x)
  (if (p12a6-r-lt-p
       ctx x (p12a6-r-zero ctx))
      (p12a6-r-neg-value ctx x)
    x))

(defun p12a6-positive-real-p (ctx x)
  (and
   (p12a6-member-p (p12a6-r-carrier ctx) x)
   (p12a6-r-lt-p
    ctx (p12a6-r-zero ctx) x)))

(defun p12a6-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p12a6-r-zero ctx)
    (p12a6-r-add-value
     ctx
     (p12a6-r-one ctx)
     (p12a6-nat-cast ctx (- n 1)))))

;; Epsilon-delta continuity for the product topology on the full plane.

(defun-sk p12a6-continuity-neighborhood-p
    (ctx function x y epsilon radius)
  (forall (u v)
    (implies
     (and
      (p12a6-member-p (p12a6-r-carrier ctx) u)
      (p12a6-member-p (p12a6-r-carrier ctx) v)
      (p12a6-r-lt-p
       ctx
       (p12a6-r-abs-value
        ctx (p12a6-r-sub-value ctx u x))
       radius)
      (p12a6-r-lt-p
       ctx
       (p12a6-r-abs-value
        ctx (p12a6-r-sub-value ctx v y))
       radius))
     (p12a6-r-lt-p
      ctx
      (p12a6-r-abs-value
       ctx
       (p12a6-r-sub-value
        ctx
        (p12a6-function-value function u v)
        (p12a6-function-value function x y)))
      epsilon))))

(defun-sk p12a6-continuity-radius-exists-p
    (ctx function x y epsilon)
  (exists (radius)
    (and
     (p12a6-positive-real-p ctx radius)
     (p12a6-continuity-neighborhood-p
      ctx function x y epsilon radius))))

(defun-sk p12a6-continuous-at-p
    (ctx function x y)
  (forall (epsilon)
    (implies
     (p12a6-positive-real-p ctx epsilon)
     (p12a6-continuity-radius-exists-p
      ctx function x y epsilon))))

(defun-sk p12a6-continuous-p (ctx function)
  (forall (x y)
    (implies
     (and
      (p12a6-member-p (p12a6-r-carrier ctx) x)
      (p12a6-member-p (p12a6-r-carrier ctx) y))
     (p12a6-continuous-at-p
      ctx function x y))))

(defun p12a6-admissible-function-p (ctx function)
  (and
   (tamep-functionp function)
   (p12a6-real-plane-function-p
    (p12a6-r-carrier ctx) function)
   (p12a6-continuous-p ctx function)))

;; Uniform right-endpoint double Riemann sums on [x1,x2] x [y1,y2].

(defun p12a6-row-sum
    (ctx function x1 y1 delta-x delta-y
         x-index remaining-y)
  (declare (xargs :measure (nfix remaining-y)))
  (if (zp remaining-y)
      (p12a6-r-zero ctx)
    (let* ((x
            (p12a6-r-add-value
             ctx x1
             (p12a6-r-mul-value
              ctx
              (p12a6-nat-cast ctx x-index)
              delta-x)))
           (y
            (p12a6-r-add-value
             ctx y1
             (p12a6-r-mul-value
              ctx
              (p12a6-nat-cast ctx remaining-y)
              delta-y))))
      (p12a6-r-add-value
       ctx
       (p12a6-function-value function x y)
       (p12a6-row-sum
        ctx function x1 y1 delta-x delta-y
        x-index (- remaining-y 1))))))

(defun p12a6-grid-sum
    (ctx function x1 y1 delta-x delta-y
         subdivisions remaining-x)
  (declare (xargs :measure (nfix remaining-x)))
  (if (zp remaining-x)
      (p12a6-r-zero ctx)
    (p12a6-r-add-value
     ctx
     (p12a6-row-sum
      ctx function x1 y1 delta-x delta-y
      remaining-x subdivisions)
     (p12a6-grid-sum
      ctx function x1 y1 delta-x delta-y
      subdivisions (- remaining-x 1)))))

(defun p12a6-integral-approx
    (ctx function x1 x2 y1 y2 subdivisions)
  (if (posp subdivisions)
      (let* ((denominator
              (p12a6-nat-cast ctx subdivisions))
             (delta-x
              (p12a6-r-div-value
               ctx
               (p12a6-r-sub-value ctx x2 x1)
               denominator))
             (delta-y
              (p12a6-r-div-value
               ctx
               (p12a6-r-sub-value ctx y2 y1)
               denominator))
             (sum
              (p12a6-grid-sum
               ctx function x1 y1 delta-x delta-y
               subdivisions subdivisions)))
        (p12a6-r-mul-value
         ctx
         (p12a6-r-mul-value ctx delta-x delta-y)
         sum))
    (p12a6-r-zero ctx)))

(defun-sk p12a6-integral-zero-tail-p
    (ctx function x1 x2 y1 y2 epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p12a6-r-lt-p
      ctx
      (p12a6-r-abs-value
       ctx
       (p12a6-integral-approx
        ctx function x1 x2 y1 y2 subdivisions))
      epsilon))))

(defun-sk p12a6-integral-zero-cutoff-exists-p
    (ctx function x1 x2 y1 y2 epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p12a6-integral-zero-tail-p
      ctx function x1 x2 y1 y2 epsilon cutoff))))

(defun-sk p12a6-integral-is-zero-p
    (ctx function x1 x2 y1 y2)
  (forall (epsilon)
    (implies
     (p12a6-positive-real-p ctx epsilon)
     (p12a6-integral-zero-cutoff-exists-p
      ctx function x1 x2 y1 y2 epsilon))))

(defun p12a6-unit-area-rectangle-p
    (ctx x1 x2 y1 y2)
  (and
   (p12a6-member-p (p12a6-r-carrier ctx) x1)
   (p12a6-member-p (p12a6-r-carrier ctx) x2)
   (p12a6-member-p (p12a6-r-carrier ctx) y1)
   (p12a6-member-p (p12a6-r-carrier ctx) y2)
   (p12a6-r-lt-p ctx x1 x2)
   (p12a6-r-lt-p ctx y1 y2)
   (equal
    (p12a6-r-mul-value
     ctx
     (p12a6-r-sub-value ctx x2 x1)
     (p12a6-r-sub-value ctx y2 y1))
    (p12a6-r-one ctx))))

(defun-sk p12a6-unit-rectangle-integrals-zero-p
    (ctx function)
  (forall (x1 x2 y1 y2)
    (implies
     (p12a6-unit-area-rectangle-p
      ctx x1 x2 y1 y2)
     (p12a6-integral-is-zero-p
      ctx function x1 x2 y1 y2))))

(defun-sk p12a6-identically-zero-p (ctx function)
  (forall (x y)
    (implies
     (and
      (p12a6-member-p (p12a6-r-carrier ctx) x)
      (p12a6-member-p (p12a6-r-carrier ctx) y))
     (equal
      (p12a6-function-value function x y)
      (p12a6-r-zero ctx)))))

;; The source predicate p and its defining equivalence are unfolded. Since the
;; published answer represented by putnam_2012_a6_solution is True, the source
;; biconditional is exactly this universally quantified implication.

(defun-sk p12a6-all-admissible-functions-zero-p (ctx)
  (forall (function)
    (implies
     (and
      (p12a6-admissible-function-p ctx function)
      (p12a6-unit-rectangle-integrals-zero-p
       ctx function))
     (p12a6-identically-zero-p ctx function))))

(defun putnambench-putnam-2012-a6-statement (ctx)
  (implies
   (p12a6-context-p ctx)
   (p12a6-all-admissible-functions-zero-p ctx)))

(value-triple :itpeval-statement-checked)
:q
