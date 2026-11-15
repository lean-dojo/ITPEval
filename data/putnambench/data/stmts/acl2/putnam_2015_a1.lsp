;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_a1:
;; a maximum-area triangle inscribed in the positive branch of xy = 1 has
;; equal areas between the hyperbola and its two adjacent chords. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context is a Dedekind-complete ordered field, hence a presentation of
;; the real field. The source hyperbola and chord function are unfolded. The
;; triangle area is its determinant formula, and each source Lebesgue integral
;; is represented by the equivalent limit of uniform right-endpoint Riemann
;; sums; the endpoints do not affect these continuous integrands.

(defun p15a1-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p15a1-unary-value (operation x)
  (apply$ operation (list x)))

(defun p15a1-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p15a1-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p15a1-member-p carrier x))))

(defun-sk p15a1-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p15a1-member-p carrier x)
      (p15a1-member-p carrier y)
      (p15a1-member-p carrier z))
     (and
      (p15a1-member-p
       carrier (p15a1-binary-value add x y))
      (p15a1-member-p
       carrier (p15a1-binary-value multiply x y))
      (p15a1-member-p
       carrier (p15a1-unary-value negate x))
      (p15a1-member-p
       carrier (p15a1-unary-value inverse x))
      (equal
       (p15a1-binary-value
        add (p15a1-binary-value add x y) z)
       (p15a1-binary-value
        add x (p15a1-binary-value add y z)))
      (equal
       (p15a1-binary-value add x y)
       (p15a1-binary-value add y x))
      (equal (p15a1-binary-value add x zero) x)
      (equal
       (p15a1-binary-value
        add x (p15a1-unary-value negate x))
       zero)
      (equal
       (p15a1-binary-value
        multiply
        (p15a1-binary-value multiply x y)
        z)
       (p15a1-binary-value
        multiply
        x
        (p15a1-binary-value multiply y z)))
      (equal
       (p15a1-binary-value multiply x y)
       (p15a1-binary-value multiply y x))
      (equal
       (p15a1-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p15a1-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p15a1-binary-value
         multiply x (p15a1-unary-value inverse x))
        one))
      (equal
       (p15a1-binary-value
        multiply x (p15a1-binary-value add y z))
       (p15a1-binary-value
        add
        (p15a1-binary-value multiply x y)
        (p15a1-binary-value multiply x z)))))))

(defun-sk p15a1-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p15a1-member-p carrier x)
      (p15a1-member-p carrier y)
      (p15a1-member-p carrier z))
     (and
      (not (p15a1-binary-value less x x))
      (or
       (equal x y)
       (p15a1-binary-value less x y)
       (p15a1-binary-value less y x))
      (implies
       (and
        (p15a1-binary-value less x y)
        (p15a1-binary-value less y z))
       (p15a1-binary-value less x z))
      (implies
       (p15a1-binary-value less x y)
       (p15a1-binary-value
        less
        (p15a1-binary-value add x z)
        (p15a1-binary-value add y z)))
      (implies
       (and
        (p15a1-binary-value less zero x)
        (p15a1-binary-value less zero y))
       (p15a1-binary-value
        less
        zero
        (p15a1-binary-value multiply x y)))))))

(defun-sk p15a1-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p15a1-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p15a1-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p15a1-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p15a1-binary-value less bound x)))))

(defun-sk p15a1-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p15a1-member-p carrier bound)
     (p15a1-upper-bound-p
      carrier less set bound))))

(defun-sk p15a1-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p15a1-member-p carrier bound)
      (p15a1-upper-bound-p
       carrier less set bound))
     (not
      (p15a1-binary-value
       less bound supremum)))))

(defun p15a1-supremum-p
    (carrier less set supremum)
  (and
   (p15a1-member-p carrier supremum)
   (p15a1-upper-bound-p
    carrier less set supremum)
   (p15a1-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p15a1-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p15a1-supremum-p
     carrier less set supremum)))

(defun-sk p15a1-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p15a1-valid-set-p carrier set)
      (p15a1-set-nonempty-p carrier set)
      (p15a1-bounded-above-p carrier less set))
     (p15a1-has-supremum-p
      carrier less set))))

(defun p15a1-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p15a1-member-p carrier zero)
   (p15a1-member-p carrier one)
   (not (equal zero one))
   (p15a1-field-laws-p
    carrier add multiply negate inverse zero one)
   (p15a1-order-laws-p
    carrier add multiply zero less)
   (p15a1-binary-value less zero one)
   (p15a1-dedekind-complete-p carrier less)))

;; Real-field context and arithmetic.

(defun p15a1-r-carrier (ctx) (nth 0 ctx))
(defun p15a1-r-zero (ctx) (nth 1 ctx))
(defun p15a1-r-one (ctx) (nth 2 ctx))
(defun p15a1-r-add (ctx) (nth 3 ctx))
(defun p15a1-r-mul (ctx) (nth 4 ctx))
(defun p15a1-r-neg (ctx) (nth 5 ctx))
(defun p15a1-r-inv (ctx) (nth 6 ctx))
(defun p15a1-r-lt (ctx) (nth 7 ctx))

(defun p15a1-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p15a1-real-field-p
    (p15a1-r-carrier ctx)
    (p15a1-r-add ctx)
    (p15a1-r-mul ctx)
    (p15a1-r-neg ctx)
    (p15a1-r-inv ctx)
    (p15a1-r-zero ctx)
    (p15a1-r-one ctx)
    (p15a1-r-lt ctx))))

(defun p15a1-r-add-value (ctx x y)
  (p15a1-binary-value (p15a1-r-add ctx) x y))

(defun p15a1-r-mul-value (ctx x y)
  (p15a1-binary-value (p15a1-r-mul ctx) x y))

(defun p15a1-r-neg-value (ctx x)
  (p15a1-unary-value (p15a1-r-neg ctx) x))

(defun p15a1-r-inv-value (ctx x)
  (p15a1-unary-value (p15a1-r-inv ctx) x))

(defun p15a1-r-sub-value (ctx x y)
  (p15a1-r-add-value
   ctx x (p15a1-r-neg-value ctx y)))

(defun p15a1-r-div-value (ctx x y)
  (p15a1-r-mul-value
   ctx x (p15a1-r-inv-value ctx y)))

(defun p15a1-r-lt-p (ctx x y)
  (if (p15a1-binary-value
       (p15a1-r-lt ctx) x y)
      t nil))

(defun p15a1-r-le-p (ctx x y)
  (not (p15a1-r-lt-p ctx y x)))

(defun p15a1-r-abs-value (ctx x)
  (if (p15a1-r-lt-p
       ctx x (p15a1-r-zero ctx))
      (p15a1-r-neg-value ctx x)
    x))

(defun p15a1-positive-real-p (ctx x)
  (and
   (p15a1-member-p (p15a1-r-carrier ctx) x)
   (p15a1-r-lt-p
    ctx (p15a1-r-zero ctx) x)))

(defun p15a1-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p15a1-r-zero ctx)
    (p15a1-r-add-value
     ctx
     (p15a1-r-one ctx)
     (p15a1-nat-cast ctx (- n 1)))))

;; Points, the positive hyperbola branch, and triangle area.

(defun p15a1-point-p (ctx point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (p15a1-member-p
    (p15a1-r-carrier ctx) (nth 0 point))
   (p15a1-member-p
    (p15a1-r-carrier ctx) (nth 1 point))))

(defun p15a1-point-x (point)
  (nth 0 point))

(defun p15a1-point-y (point)
  (nth 1 point))

(defun p15a1-on-hyperbola-p (ctx point)
  (and
   (p15a1-point-p ctx point)
   (p15a1-positive-real-p
    ctx (p15a1-point-x point))
   (equal
    (p15a1-point-y point)
    (p15a1-r-inv-value
     ctx (p15a1-point-x point)))))

(defun p15a1-two (ctx)
  (p15a1-r-add-value
   ctx (p15a1-r-one ctx) (p15a1-r-one ctx)))

(defun p15a1-triangle-double-area
    (ctx a p b)
  (p15a1-r-abs-value
   ctx
   (p15a1-r-sub-value
    ctx
    (p15a1-r-mul-value
     ctx
     (p15a1-r-sub-value
      ctx (p15a1-point-x p) (p15a1-point-x a))
     (p15a1-r-sub-value
      ctx (p15a1-point-y b) (p15a1-point-y a)))
    (p15a1-r-mul-value
     ctx
     (p15a1-r-sub-value
      ctx (p15a1-point-y p) (p15a1-point-y a))
     (p15a1-r-sub-value
      ctx (p15a1-point-x b) (p15a1-point-x a))))))

(defun p15a1-triangle-area
    (ctx a p b)
  (p15a1-r-div-value
   ctx
   (p15a1-triangle-double-area ctx a p b)
   (p15a1-two ctx)))

(defun p15a1-interior-hyperbola-point-p
    (ctx a b point)
  (and
   (p15a1-on-hyperbola-p ctx point)
   (p15a1-r-lt-p
    ctx (p15a1-point-x a) (p15a1-point-x point))
   (p15a1-r-lt-p
    ctx (p15a1-point-x point) (p15a1-point-x b))))

(defun-sk p15a1-maximizes-triangle-area-p
    (ctx a b p)
  (forall (p-prime)
    (implies
     (p15a1-interior-hyperbola-point-p
      ctx a b p-prime)
     (p15a1-r-le-p
      ctx
      (p15a1-triangle-area ctx a p-prime b)
      (p15a1-triangle-area ctx a p b)))))

;; The affine chord through LEFT and RIGHT, and its difference from 1/x.

(defun p15a1-chord-value
    (ctx left right x)
  (p15a1-r-add-value
   ctx
   (p15a1-r-mul-value
    ctx
    (p15a1-r-div-value
     ctx
     (p15a1-r-sub-value
      ctx
      (p15a1-point-y right)
      (p15a1-point-y left))
     (p15a1-r-sub-value
      ctx
      (p15a1-point-x right)
      (p15a1-point-x left)))
    (p15a1-r-sub-value
     ctx x (p15a1-point-x left)))
   (p15a1-point-y left)))

(defun p15a1-region-integrand
    (ctx left right x)
  (p15a1-r-sub-value
   ctx
   (p15a1-chord-value ctx left right x)
   (p15a1-r-inv-value ctx x)))

;; Uniform right-endpoint Riemann sums on [START, END].

(defun p15a1-riemann-sum
    (ctx left right start delta remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p15a1-r-zero ctx)
    (p15a1-r-add-value
     ctx
     (p15a1-region-integrand
      ctx left right
      (p15a1-r-add-value
       ctx start
       (p15a1-r-mul-value
        ctx
        (p15a1-nat-cast ctx remaining)
        delta)))
     (p15a1-riemann-sum
      ctx left right start delta (- remaining 1)))))

(defun p15a1-integral-approx
    (ctx left right start end subdivisions)
  (if (posp subdivisions)
      (let ((delta
             (p15a1-r-div-value
              ctx
              (p15a1-r-sub-value ctx end start)
              (p15a1-nat-cast ctx subdivisions))))
        (p15a1-r-mul-value
         ctx
         delta
         (p15a1-riemann-sum
          ctx left right start delta subdivisions)))
    (p15a1-r-zero ctx)))

(defun-sk p15a1-integral-tail-p
    (ctx left right start end value epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p15a1-r-lt-p
      ctx
      (p15a1-r-abs-value
       ctx
       (p15a1-r-sub-value
        ctx
        (p15a1-integral-approx
         ctx left right start end subdivisions)
        value))
      epsilon))))

(defun-sk p15a1-integral-cutoff-exists-p
    (ctx left right start end value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p15a1-integral-tail-p
      ctx left right start end value epsilon cutoff))))

(defun-sk p15a1-integral-value-p
    (ctx left right start end value)
  (forall (epsilon)
    (implies
     (p15a1-positive-real-p ctx epsilon)
     (p15a1-integral-cutoff-exists-p
      ctx left right start end value epsilon))))

(defun-sk p15a1-equal-region-integrals-p
    (ctx a p b)
  (exists (common-value)
    (and
     (p15a1-member-p
      (p15a1-r-carrier ctx) common-value)
     (p15a1-integral-value-p
      ctx a p
      (p15a1-point-x a)
      (p15a1-point-x p)
      common-value)
     (p15a1-integral-value-p
      ctx p b
      (p15a1-point-x p)
      (p15a1-point-x b)
      common-value))))

(defun putnambench-putnam-2015-a1-statement
    (ctx a b p)
  (implies
   (and
    (p15a1-context-p ctx)
    (p15a1-on-hyperbola-p ctx a)
    (p15a1-on-hyperbola-p ctx b)
    (p15a1-r-lt-p
     ctx (p15a1-point-x a) (p15a1-point-x b))
    (p15a1-interior-hyperbola-point-p ctx a b p)
    (p15a1-maximizes-triangle-area-p ctx a b p))
   (p15a1-equal-region-integrals-p ctx a p b)))

(value-triple :itpeval-statement-checked)
:q
