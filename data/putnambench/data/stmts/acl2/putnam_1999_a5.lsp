;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_a5:
;; a uniform real constant bounds the value at zero of every degree-1999 real
;; polynomial by its L1 integral on [-1,1]. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A context below is a Dedekind-complete ordered field, hence isomorphic to
;; the real field. Coefficient lists contain arbitrary elements of its carrier,
;; not rational approximations. The interval integral is characterized by the
;; limit of all sufficiently fine right-endpoint Riemann sums. For polynomial
;; absolute values this is exactly the source interval Lebesgue integral.

(defun p99a5-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p99a5-unary-value (operation x)
  (apply$ operation (list x)))

(defun p99a5-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p99a5-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p99a5-member-p carrier x))))

(defun-sk p99a5-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p99a5-member-p carrier x)
      (p99a5-member-p carrier y)
      (p99a5-member-p carrier z))
     (and
      (p99a5-member-p
       carrier (p99a5-binary-value add x y))
      (p99a5-member-p
       carrier (p99a5-binary-value multiply x y))
      (p99a5-member-p
       carrier (p99a5-unary-value negate x))
      (implies
       (not (equal x zero))
       (p99a5-member-p
        carrier (p99a5-unary-value inverse x)))
      (equal
       (p99a5-binary-value
        add (p99a5-binary-value add x y) z)
       (p99a5-binary-value
        add x (p99a5-binary-value add y z)))
      (equal
       (p99a5-binary-value add x y)
       (p99a5-binary-value add y x))
      (equal
       (p99a5-binary-value add x zero)
       x)
      (equal
       (p99a5-binary-value
        add x (p99a5-unary-value negate x))
       zero)
      (equal
       (p99a5-binary-value
        multiply
        (p99a5-binary-value multiply x y)
        z)
       (p99a5-binary-value
        multiply
        x
        (p99a5-binary-value multiply y z)))
      (equal
       (p99a5-binary-value multiply x y)
       (p99a5-binary-value multiply y x))
      (equal
       (p99a5-binary-value multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (p99a5-binary-value
         multiply x (p99a5-unary-value inverse x))
        one))
      (equal
       (p99a5-binary-value
        multiply x (p99a5-binary-value add y z))
       (p99a5-binary-value
        add
        (p99a5-binary-value multiply x y)
        (p99a5-binary-value multiply x z)))))))

(defun-sk p99a5-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p99a5-member-p carrier x)
      (p99a5-member-p carrier y)
      (p99a5-member-p carrier z))
     (and
      (not (p99a5-binary-value less x x))
      (or
       (equal x y)
       (p99a5-binary-value less x y)
       (p99a5-binary-value less y x))
      (implies
       (and
        (p99a5-binary-value less x y)
        (p99a5-binary-value less y z))
       (p99a5-binary-value less x z))
      (implies
       (p99a5-binary-value less x y)
       (p99a5-binary-value
        less
        (p99a5-binary-value add x z)
        (p99a5-binary-value add y z)))
      (implies
       (and
        (p99a5-binary-value less zero x)
        (p99a5-binary-value less zero y))
       (p99a5-binary-value
        less
        zero
        (p99a5-binary-value multiply x y)))))))

(defun-sk p99a5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p99a5-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p99a5-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p99a5-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p99a5-binary-value less bound x)))))

(defun-sk p99a5-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p99a5-member-p carrier bound)
     (p99a5-upper-bound-p
      carrier less set bound))))

(defun-sk p99a5-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (p99a5-member-p carrier supremum)
     (p99a5-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (p99a5-member-p carrier bound)
       (p99a5-upper-bound-p
        carrier less set bound))
      (not
       (p99a5-binary-value
        less bound supremum))))))

(defun-sk p99a5-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p99a5-supremum-p
     carrier less set supremum)))

(defun-sk p99a5-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p99a5-valid-set-p carrier set)
      (p99a5-set-nonempty-p carrier set)
      (p99a5-bounded-above-p carrier less set))
     (p99a5-has-supremum-p
      carrier less set))))

(defun p99a5-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p99a5-member-p carrier zero)
   (p99a5-member-p carrier one)
   (not (equal zero one))
   (p99a5-field-laws-p
    carrier add multiply negate inverse zero one)
   (p99a5-order-laws-p
    carrier add multiply zero less)
   (p99a5-binary-value less zero one)
   (p99a5-dedekind-complete-p carrier less)))

(defun p99a5-r-carrier (ctx) (nth 0 ctx))
(defun p99a5-r-zero (ctx) (nth 1 ctx))
(defun p99a5-r-one (ctx) (nth 2 ctx))
(defun p99a5-r-add (ctx) (nth 3 ctx))
(defun p99a5-r-mul (ctx) (nth 4 ctx))
(defun p99a5-r-neg (ctx) (nth 5 ctx))
(defun p99a5-r-inv (ctx) (nth 6 ctx))
(defun p99a5-r-lt (ctx) (nth 7 ctx))

(defun p99a5-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p99a5-real-field-p
    (p99a5-r-carrier ctx)
    (p99a5-r-add ctx)
    (p99a5-r-mul ctx)
    (p99a5-r-neg ctx)
    (p99a5-r-inv ctx)
    (p99a5-r-zero ctx)
    (p99a5-r-one ctx)
    (p99a5-r-lt ctx))))

(defun p99a5-r-add-value (ctx x y)
  (p99a5-binary-value (p99a5-r-add ctx) x y))

(defun p99a5-r-mul-value (ctx x y)
  (p99a5-binary-value (p99a5-r-mul ctx) x y))

(defun p99a5-r-neg-value (ctx x)
  (p99a5-unary-value (p99a5-r-neg ctx) x))

(defun p99a5-r-inv-value (ctx x)
  (p99a5-unary-value (p99a5-r-inv ctx) x))

(defun p99a5-r-sub-value (ctx x y)
  (p99a5-r-add-value
   ctx x (p99a5-r-neg-value ctx y)))

(defun p99a5-r-div-value (ctx x y)
  (p99a5-r-mul-value
   ctx x (p99a5-r-inv-value ctx y)))

(defun p99a5-r-lt-p (ctx x y)
  (if (p99a5-binary-value
       (p99a5-r-lt ctx) x y)
      t nil))

(defun p99a5-r-le-p (ctx x y)
  (not (p99a5-r-lt-p ctx y x)))

(defun p99a5-r-abs-value (ctx x)
  (if (p99a5-r-lt-p
       ctx x (p99a5-r-zero ctx))
      (p99a5-r-neg-value ctx x)
    x))

(defun p99a5-positive-real-p (ctx x)
  (and
   (p99a5-member-p (p99a5-r-carrier ctx) x)
   (p99a5-r-lt-p
    ctx (p99a5-r-zero ctx) x)))

(defun p99a5-carrier-list-p (ctx values)
  (if (consp values)
      (and
       (p99a5-member-p
        (p99a5-r-carrier ctx) (car values))
       (p99a5-carrier-list-p ctx (cdr values)))
    (equal values nil)))

(defun p99a5-degree-1999-polynomial-p
    (ctx coefficients)
  (and
   (true-listp coefficients)
   (equal (len coefficients) 2000)
   (p99a5-carrier-list-p ctx coefficients)
   (not
    (equal
     (car (last coefficients))
     (p99a5-r-zero ctx)))))

(defun p99a5-polynomial-value
    (ctx coefficients x)
  (if (consp coefficients)
      (p99a5-r-add-value
       ctx
       (car coefficients)
       (p99a5-r-mul-value
        ctx
        x
        (p99a5-polynomial-value
         ctx (cdr coefficients) x)))
    (p99a5-r-zero ctx)))

(defun p99a5-nat-cast (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p99a5-r-zero ctx)
    (p99a5-r-add-value
     ctx
     (p99a5-r-one ctx)
     (p99a5-nat-cast ctx (- n 1)))))

(defun p99a5-two (ctx)
  (p99a5-r-add-value
   ctx
   (p99a5-r-one ctx)
   (p99a5-r-one ctx)))

(defun p99a5-minus-one (ctx)
  (p99a5-r-neg-value
   ctx (p99a5-r-one ctx)))

(defun p99a5-grid-point
    (ctx subdivisions index)
  (p99a5-r-add-value
   ctx
   (p99a5-minus-one ctx)
   (p99a5-r-mul-value
    ctx
    (p99a5-two ctx)
    (p99a5-r-div-value
     ctx
     (p99a5-nat-cast ctx index)
     (p99a5-nat-cast ctx subdivisions)))))

(defun p99a5-riemann-sum-terms
    (ctx coefficients subdivisions remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p99a5-r-zero ctx)
    (p99a5-r-add-value
     ctx
     (p99a5-r-abs-value
      ctx
      (p99a5-polynomial-value
       ctx
       coefficients
       (p99a5-grid-point
        ctx subdivisions remaining)))
     (p99a5-riemann-sum-terms
      ctx coefficients subdivisions (- remaining 1)))))

(defun p99a5-riemann-approx
    (ctx coefficients subdivisions)
  (if (posp subdivisions)
      (p99a5-r-mul-value
       ctx
       (p99a5-r-div-value
        ctx
        (p99a5-two ctx)
        (p99a5-nat-cast ctx subdivisions))
       (p99a5-riemann-sum-terms
        ctx coefficients subdivisions subdivisions))
    (p99a5-r-zero ctx)))

(defun-sk p99a5-integral-tail-p
    (ctx coefficients integral epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p99a5-r-lt-p
      ctx
      (p99a5-r-abs-value
       ctx
       (p99a5-r-sub-value
        ctx
        (p99a5-riemann-approx
         ctx coefficients subdivisions)
        integral))
      epsilon))))

(defun-sk p99a5-integral-cutoff-exists-p
    (ctx coefficients integral epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p99a5-integral-tail-p
      ctx coefficients integral epsilon cutoff))))

(defun-sk p99a5-integral-converges-to-p
    (ctx coefficients integral)
  (forall (epsilon)
    (implies
     (p99a5-positive-real-p ctx epsilon)
     (p99a5-integral-cutoff-exists-p
      ctx coefficients integral epsilon))))

(defun p99a5-integral-value-p
    (ctx coefficients integral)
  (and
   (p99a5-member-p
    (p99a5-r-carrier ctx) integral)
   (p99a5-integral-converges-to-p
    ctx coefficients integral)))

(defun-sk p99a5-polynomial-bound-p
    (ctx constant coefficients)
  (exists (integral)
    (and
     (p99a5-integral-value-p
      ctx coefficients integral)
     (p99a5-r-le-p
      ctx
      (p99a5-r-abs-value
       ctx
       (p99a5-polynomial-value
        ctx coefficients (p99a5-r-zero ctx)))
      (p99a5-r-mul-value
       ctx constant integral)))))

(defun-sk p99a5-constant-bounds-all-p
    (ctx constant)
  (forall (coefficients)
    (implies
     (p99a5-degree-1999-polynomial-p
      ctx coefficients)
     (p99a5-polynomial-bound-p
      ctx constant coefficients))))

(defun-sk p99a5-bound-constant-exists-p (ctx)
  (exists (constant)
    (and
     (p99a5-member-p
      (p99a5-r-carrier ctx) constant)
     (p99a5-constant-bounds-all-p
      ctx constant))))

(defun putnambench-putnam-1999-a5-statement (ctx)
  (implies
   (p99a5-context-p ctx)
   (p99a5-bound-constant-exists-p ctx)))

(value-triple :itpeval-statement-checked)
:q
