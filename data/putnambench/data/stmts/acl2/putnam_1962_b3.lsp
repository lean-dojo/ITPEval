;; Statement-only formalization of PutnamBench corpus artifact putnam_1962_b3:
;; a convex subset of the real plane containing the origin, topologically
;; closed or containing the origin in its interior, is bounded when every ray
;; from the origin contains a point outside the set. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real scalars up to the
;; unique ordered-field isomorphism. Plane points are coordinate pairs, and
;; the arbitrary set is a tame APPLY$ characteristic-function object.
;; DEFUN-SK retains every universal and existential quantifier internally.

(defun putnam-1962-b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1962-b3-unary-value (operation x)
  (apply$ operation (list x)))

(defun putnam-1962-b3-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk putnam-1962-b3-valid-scalar-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (putnam-1962-b3-member-p carrier x))))

(defun-sk putnam-1962-b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1962-b3-member-p carrier x)
      (putnam-1962-b3-member-p carrier y)
      (putnam-1962-b3-member-p carrier z))
     (and
      (putnam-1962-b3-member-p
       carrier
       (putnam-1962-b3-binary-value add x y))
      (putnam-1962-b3-member-p
       carrier
       (putnam-1962-b3-binary-value multiply x y))
      (putnam-1962-b3-member-p
       carrier
       (putnam-1962-b3-unary-value negate x))
      (implies
       (not (equal x zero))
       (putnam-1962-b3-member-p
        carrier
        (putnam-1962-b3-unary-value inverse x)))
      (equal
       (putnam-1962-b3-binary-value
        add
        (putnam-1962-b3-binary-value add x y)
        z)
       (putnam-1962-b3-binary-value
        add
        x
        (putnam-1962-b3-binary-value add y z)))
      (equal
       (putnam-1962-b3-binary-value add x y)
       (putnam-1962-b3-binary-value add y x))
      (equal
       (putnam-1962-b3-binary-value add x zero)
       x)
      (equal
       (putnam-1962-b3-binary-value
        add x (putnam-1962-b3-unary-value negate x))
       zero)
      (equal
       (putnam-1962-b3-binary-value
        multiply
        (putnam-1962-b3-binary-value multiply x y)
        z)
       (putnam-1962-b3-binary-value
        multiply
        x
        (putnam-1962-b3-binary-value multiply y z)))
      (equal
       (putnam-1962-b3-binary-value multiply x y)
       (putnam-1962-b3-binary-value multiply y x))
      (equal
       (putnam-1962-b3-binary-value multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1962-b3-binary-value
         multiply
         x
         (putnam-1962-b3-unary-value inverse x))
        one))
      (equal
       (putnam-1962-b3-binary-value
        multiply
        x
        (putnam-1962-b3-binary-value add y z))
       (putnam-1962-b3-binary-value
        add
        (putnam-1962-b3-binary-value multiply x y)
        (putnam-1962-b3-binary-value multiply x z)))))))

(defun-sk putnam-1962-b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (putnam-1962-b3-member-p carrier x)
      (putnam-1962-b3-member-p carrier y)
      (putnam-1962-b3-member-p carrier z))
     (and
      (not (putnam-1962-b3-binary-value less x x))
      (or
       (equal x y)
       (putnam-1962-b3-binary-value less x y)
       (putnam-1962-b3-binary-value less y x))
      (implies
       (and
        (putnam-1962-b3-binary-value less x y)
        (putnam-1962-b3-binary-value less y z))
       (putnam-1962-b3-binary-value less x z))
      (implies
       (putnam-1962-b3-binary-value less x y)
       (putnam-1962-b3-binary-value
        less
        (putnam-1962-b3-binary-value add x z)
        (putnam-1962-b3-binary-value add y z)))
      (implies
       (and
        (putnam-1962-b3-binary-value less zero x)
        (putnam-1962-b3-binary-value less zero y))
       (putnam-1962-b3-binary-value
        less
        zero
        (putnam-1962-b3-binary-value multiply x y)))))))

(defun-sk putnam-1962-b3-scalar-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1962-b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1962-b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1962-b3-member-p carrier x)
      (apply$ set (list x)))
     (not
      (putnam-1962-b3-binary-value less bound x)))))

(defun-sk putnam-1962-b3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1962-b3-member-p carrier bound)
     (putnam-1962-b3-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1962-b3-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1962-b3-member-p carrier supremum)
     (putnam-1962-b3-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1962-b3-member-p carrier bound)
       (putnam-1962-b3-upper-bound-p
        carrier less set bound))
      (not
       (putnam-1962-b3-binary-value
        less bound supremum))))))

(defun-sk putnam-1962-b3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1962-b3-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1962-b3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1962-b3-valid-scalar-set-p carrier set)
      (putnam-1962-b3-scalar-set-nonempty-p carrier set)
      (putnam-1962-b3-bounded-above-p
       carrier less set))
     (putnam-1962-b3-has-supremum-p
      carrier less set))))

(defun putnam-1962-b3-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1962-b3-member-p carrier zero)
   (putnam-1962-b3-member-p carrier one)
   (not (equal zero one))
   (putnam-1962-b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (putnam-1962-b3-order-laws-p
    carrier add multiply zero less)
   (putnam-1962-b3-binary-value less zero one)
   (putnam-1962-b3-dedekind-complete-p
    carrier less)))

(defun putnam-1962-b3-r-carrier (ctx) (nth 0 ctx))
(defun putnam-1962-b3-r-zero (ctx) (nth 1 ctx))
(defun putnam-1962-b3-r-one (ctx) (nth 2 ctx))
(defun putnam-1962-b3-r-add (ctx) (nth 3 ctx))
(defun putnam-1962-b3-r-mul (ctx) (nth 4 ctx))
(defun putnam-1962-b3-r-neg (ctx) (nth 5 ctx))
(defun putnam-1962-b3-r-inv (ctx) (nth 6 ctx))
(defun putnam-1962-b3-r-lt (ctx) (nth 7 ctx))

(defun putnam-1962-b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (putnam-1962-b3-real-field-p
    (putnam-1962-b3-r-carrier ctx)
    (putnam-1962-b3-r-add ctx)
    (putnam-1962-b3-r-mul ctx)
    (putnam-1962-b3-r-neg ctx)
    (putnam-1962-b3-r-inv ctx)
    (putnam-1962-b3-r-zero ctx)
    (putnam-1962-b3-r-one ctx)
    (putnam-1962-b3-r-lt ctx))))

(defun putnam-1962-b3-r-add-value (ctx x y)
  (putnam-1962-b3-binary-value
   (putnam-1962-b3-r-add ctx) x y))

(defun putnam-1962-b3-r-mul-value (ctx x y)
  (putnam-1962-b3-binary-value
   (putnam-1962-b3-r-mul ctx) x y))

(defun putnam-1962-b3-r-neg-value (ctx x)
  (putnam-1962-b3-unary-value
   (putnam-1962-b3-r-neg ctx) x))

(defun putnam-1962-b3-r-sub-value (ctx x y)
  (putnam-1962-b3-r-add-value
   ctx x (putnam-1962-b3-r-neg-value ctx y)))

(defun putnam-1962-b3-r-lt-p (ctx x y)
  (if
   (putnam-1962-b3-binary-value
    (putnam-1962-b3-r-lt ctx) x y)
   t
   nil))

(defun putnam-1962-b3-positive-scalar-p (ctx x)
  (and
   (putnam-1962-b3-member-p
    (putnam-1962-b3-r-carrier ctx) x)
   (putnam-1962-b3-r-lt-p
    ctx (putnam-1962-b3-r-zero ctx) x)))

(defun putnam-1962-b3-nonnegative-scalar-p (ctx x)
  (and
   (putnam-1962-b3-member-p
    (putnam-1962-b3-r-carrier ctx) x)
   (not
    (putnam-1962-b3-r-lt-p
     ctx x (putnam-1962-b3-r-zero ctx)))))

(defun putnam-1962-b3-square-value (ctx x)
  (putnam-1962-b3-r-mul-value ctx x x))

(defun putnam-1962-b3-point-p (ctx x y)
  (and
   (putnam-1962-b3-member-p
    (putnam-1962-b3-r-carrier ctx) x)
   (putnam-1962-b3-member-p
    (putnam-1962-b3-r-carrier ctx) y)))

(defun putnam-1962-b3-set-member-p (set x y)
  (if (apply$ set (list (cons x y))) t nil))

(defun putnam-1962-b3-squared-norm (ctx x y)
  (putnam-1962-b3-r-add-value
   ctx
   (putnam-1962-b3-square-value ctx x)
   (putnam-1962-b3-square-value ctx y)))

(defun putnam-1962-b3-squared-distance
    (ctx x y u v)
  (putnam-1962-b3-squared-norm
   ctx
   (putnam-1962-b3-r-sub-value ctx u x)
   (putnam-1962-b3-r-sub-value ctx v y)))

(defun-sk putnam-1962-b3-convex-set-p (ctx set)
  (forall (a b x y u v)
    (implies
     (and
      (putnam-1962-b3-nonnegative-scalar-p ctx a)
      (putnam-1962-b3-nonnegative-scalar-p ctx b)
      (equal
       (putnam-1962-b3-r-add-value ctx a b)
       (putnam-1962-b3-r-one ctx))
      (putnam-1962-b3-point-p ctx x y)
      (putnam-1962-b3-point-p ctx u v)
      (putnam-1962-b3-set-member-p set x y)
      (putnam-1962-b3-set-member-p set u v))
     (putnam-1962-b3-set-member-p
      set
      (putnam-1962-b3-r-add-value
       ctx
       (putnam-1962-b3-r-mul-value ctx a x)
       (putnam-1962-b3-r-mul-value ctx b u))
      (putnam-1962-b3-r-add-value
       ctx
       (putnam-1962-b3-r-mul-value ctx a y)
       (putnam-1962-b3-r-mul-value ctx b v))))))

(defun putnam-1962-b3-origin-in-set-p (ctx set)
  (putnam-1962-b3-set-member-p
   set
   (putnam-1962-b3-r-zero ctx)
   (putnam-1962-b3-r-zero ctx)))

(defun-sk putnam-1962-b3-origin-ball-subset-p
    (ctx set radius)
  (forall (x y)
    (implies
     (and
      (putnam-1962-b3-point-p ctx x y)
      (putnam-1962-b3-r-lt-p
       ctx
       (putnam-1962-b3-squared-norm ctx x y)
       (putnam-1962-b3-square-value ctx radius)))
     (putnam-1962-b3-set-member-p set x y))))

(defun-sk putnam-1962-b3-origin-interior-p (ctx set)
  (exists (radius)
    (and
     (putnam-1962-b3-positive-scalar-p ctx radius)
     (putnam-1962-b3-origin-ball-subset-p
      ctx set radius))))

(defun-sk putnam-1962-b3-outside-neighborhood-p
    (ctx set x y radius)
  (forall (u v)
    (implies
     (and
      (putnam-1962-b3-point-p ctx u v)
      (putnam-1962-b3-r-lt-p
       ctx
       (putnam-1962-b3-squared-distance
        ctx x y u v)
       (putnam-1962-b3-square-value ctx radius)))
     (not
      (putnam-1962-b3-set-member-p set u v)))))

(defun-sk putnam-1962-b3-outside-radius-exists-p
    (ctx set x y)
  (exists (radius)
    (and
     (putnam-1962-b3-positive-scalar-p ctx radius)
     (putnam-1962-b3-outside-neighborhood-p
      ctx set x y radius))))

(defun-sk putnam-1962-b3-closed-set-p (ctx set)
  (forall (x y)
    (implies
     (and
      (putnam-1962-b3-point-p ctx x y)
      (not
       (putnam-1962-b3-set-member-p set x y)))
     (putnam-1962-b3-outside-radius-exists-p
      ctx set x y))))

(defun-sk putnam-1962-b3-ray-exit-exists-p
    (ctx set x y)
  (exists (u v scale)
    (and
     (putnam-1962-b3-point-p ctx u v)
     (putnam-1962-b3-positive-scalar-p ctx scale)
     (equal
      u
      (putnam-1962-b3-r-mul-value ctx scale x))
     (equal
      v
      (putnam-1962-b3-r-mul-value ctx scale y))
     (not
      (putnam-1962-b3-set-member-p set u v)))))

(defun-sk putnam-1962-b3-every-ray-exits-p
    (ctx set)
  (forall (x y)
    (implies
     (and
      (putnam-1962-b3-point-p ctx x y)
      (not
       (and
        (equal x (putnam-1962-b3-r-zero ctx))
        (equal y (putnam-1962-b3-r-zero ctx)))))
     (putnam-1962-b3-ray-exit-exists-p
      ctx set x y))))

(defun-sk putnam-1962-b3-contained-in-origin-ball-p
    (ctx set radius)
  (forall (x y)
    (implies
     (and
      (putnam-1962-b3-point-p ctx x y)
      (putnam-1962-b3-set-member-p set x y))
     (not
      (putnam-1962-b3-r-lt-p
       ctx
       (putnam-1962-b3-square-value ctx radius)
       (putnam-1962-b3-squared-norm ctx x y))))))

(defun-sk putnam-1962-b3-bounded-set-p (ctx set)
  (exists (radius)
    (and
     (putnam-1962-b3-positive-scalar-p ctx radius)
     (putnam-1962-b3-contained-in-origin-ball-p
      ctx set radius))))

(defun putnambench-putnam-1962-b3-statement (ctx set)
  (implies
   (and
    (putnam-1962-b3-context-p ctx)
    (tamep-functionp set)
    (putnam-1962-b3-convex-set-p ctx set)
    (putnam-1962-b3-origin-in-set-p ctx set)
    (or
     (putnam-1962-b3-origin-interior-p ctx set)
     (putnam-1962-b3-closed-set-p ctx set))
    (putnam-1962-b3-every-ray-exits-p ctx set))
   (putnam-1962-b3-bounded-set-p ctx set)))

(value-triple :itpeval-statement-checked)
:q
