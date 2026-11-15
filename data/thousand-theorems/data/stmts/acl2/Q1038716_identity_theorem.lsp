;; Statement-only formalization of thousand-theorems corpus artifact Q1038716,
;; "Identity theorem": two functions analytic on neighborhoods of a
;; preconnected subset of a nontrivially normed field agree throughout the
;; subset when their coincidence points accumulate at one of its points.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Carriers, operations, sets, functions, and coefficient sequences are
;; arbitrary ACL2 objects interpreted through conservative interfaces.  Norms
;; are represented by rational upper cuts: NORM-LT records ||x|| < q for
;; positive rational q.  Thus norm values range over all nonnegative reals,
;; rather than being restricted to ACL2 rationals.

(defstub q1038716-member-p (predicate object) t)
(defstub q1038716-unary-value (function object) t)
(defstub q1038716-binary-value (function left right) t)
(defstub q1038716-norm-lt-p (norm object bound) t)

(defun q1038716-positive-rational-p (value)
  (and (rationalp value) (< 0 value)))

(defun-sk q1038716-norm-finite-p (norm object)
  (exists (bound)
    (and
     (q1038716-positive-rational-p bound)
     (q1038716-norm-lt-p norm object bound))))

(defun-sk q1038716-norm-positive-p (norm object)
  (exists (bound)
    (and
     (q1038716-positive-rational-p bound)
     (not (q1038716-norm-lt-p norm object bound)))))

(defun-sk q1038716-norm-rounded-p (norm object bound)
  (exists (smaller)
    (and
     (q1038716-positive-rational-p smaller)
     (rationalp bound)
     (< smaller bound)
     (q1038716-norm-lt-p norm object smaller))))

(defun-sk q1038716-norm-product-lt-p
    (left-norm right-norm left right bound)
  (exists (left-bound right-bound)
    (and
     (q1038716-positive-rational-p bound)
     (q1038716-positive-rational-p left-bound)
     (q1038716-positive-rational-p right-bound)
     (q1038716-norm-lt-p left-norm left left-bound)
     (q1038716-norm-lt-p right-norm right right-bound)
     (< (* left-bound right-bound) bound))))

(defun-sk q1038716-norm-cut-laws-p
    (carrier norm zero)
  (forall (x q r)
    (implies
     (q1038716-member-p carrier x)
     (and
      (implies
       (q1038716-norm-lt-p norm x q)
       (q1038716-positive-rational-p q))
      (implies
       (and
        (q1038716-norm-lt-p norm x q)
        (rationalp r)
        (< q r))
       (q1038716-norm-lt-p norm x r))
      (implies
       (q1038716-norm-lt-p norm x q)
       (q1038716-norm-rounded-p norm x q))
      (q1038716-norm-finite-p norm x)
      (iff
       (equal x zero)
       (not (q1038716-norm-positive-p norm x)))))))

;; A nontrivially normed field.

(defun-sk q1038716-field-closure-p
    (carrier add multiply negate inverse)
  (forall (x y)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y))
     (and
      (q1038716-member-p
       carrier (q1038716-binary-value add x y))
      (q1038716-member-p
       carrier (q1038716-binary-value multiply x y))
      (q1038716-member-p
       carrier (q1038716-unary-value negate x))
      (q1038716-member-p
       carrier (q1038716-unary-value inverse x))))))

(defun-sk q1038716-field-additive-laws-p
    (carrier add negate zero)
  (forall (x y z)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y)
      (q1038716-member-p carrier z))
     (and
      (equal
       (q1038716-binary-value
        add (q1038716-binary-value add x y) z)
       (q1038716-binary-value
        add x (q1038716-binary-value add y z)))
      (equal
       (q1038716-binary-value add x y)
       (q1038716-binary-value add y x))
      (equal (q1038716-binary-value add x zero) x)
      (equal
       (q1038716-binary-value
        add x (q1038716-unary-value negate x))
       zero)))))

(defun-sk q1038716-field-multiplicative-laws-p
    (carrier multiply inverse zero one)
  (forall (x y z)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y)
      (q1038716-member-p carrier z))
     (and
      (equal
       (q1038716-binary-value
        multiply (q1038716-binary-value multiply x y) z)
       (q1038716-binary-value
        multiply x (q1038716-binary-value multiply y z)))
      (equal
       (q1038716-binary-value multiply x y)
       (q1038716-binary-value multiply y x))
      (equal (q1038716-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (q1038716-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (q1038716-binary-value
         multiply x (q1038716-unary-value inverse x))
        one))))))

(defun-sk q1038716-field-distributive-p
    (carrier add multiply)
  (forall (x y z)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y)
      (q1038716-member-p carrier z))
     (equal
      (q1038716-binary-value
       multiply x (q1038716-binary-value add y z))
      (q1038716-binary-value
       add
       (q1038716-binary-value multiply x y)
       (q1038716-binary-value multiply x z))))))

(defun-sk q1038716-field-norm-zero-one-p
    (norm zero one)
  (forall (q)
    (and
     (iff
      (q1038716-norm-lt-p norm zero q)
      (q1038716-positive-rational-p q))
     (iff
      (q1038716-norm-lt-p norm one q)
      (and (rationalp q) (< 1 q))))))

(defun-sk q1038716-field-norm-negate-p
    (carrier negate norm)
  (forall (x q)
    (implies
     (q1038716-member-p carrier x)
     (iff
      (q1038716-norm-lt-p
       norm (q1038716-unary-value negate x) q)
      (q1038716-norm-lt-p norm x q)))))

(defun-sk q1038716-field-norm-add-p
    (carrier add norm)
  (forall (x y r s)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y)
      (q1038716-positive-rational-p r)
      (q1038716-positive-rational-p s)
      (q1038716-norm-lt-p norm x r)
      (q1038716-norm-lt-p norm y s))
     (q1038716-norm-lt-p
      norm (q1038716-binary-value add x y) (+ r s)))))

(defun-sk q1038716-field-norm-multiply-p
    (carrier multiply norm)
  (forall (x y q)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y))
     (iff
      (q1038716-norm-lt-p
       norm (q1038716-binary-value multiply x y) q)
      (q1038716-norm-product-lt-p
       norm norm x y q)))))

(defun-sk q1038716-field-norm-nontrivial-p
    (carrier norm)
  (exists (x q)
    (and
     (q1038716-member-p carrier x)
     (rationalp q)
     (< 1 q)
     (not (q1038716-norm-lt-p norm x q)))))

(defun q1038716-nontrivially-normed-field-p
    (carrier zero one add multiply negate inverse norm)
  (and
   (q1038716-member-p carrier zero)
   (q1038716-member-p carrier one)
   (not (equal zero one))
   (q1038716-field-closure-p
    carrier add multiply negate inverse)
   (q1038716-field-additive-laws-p carrier add negate zero)
   (q1038716-field-multiplicative-laws-p
    carrier multiply inverse zero one)
   (q1038716-field-distributive-p carrier add multiply)
   (q1038716-norm-cut-laws-p carrier norm zero)
   (q1038716-field-norm-zero-one-p norm zero one)
   (q1038716-field-norm-negate-p carrier negate norm)
   (q1038716-field-norm-add-p carrier add norm)
   (q1038716-field-norm-multiply-p carrier multiply norm)
   (q1038716-field-norm-nontrivial-p carrier norm)))

;; A normed additive commutative group and vector space over the field.

(defun-sk q1038716-space-closure-p
    (field-carrier carrier add negate scalar-multiply)
  (forall (a x y)
    (implies
     (and
      (q1038716-member-p field-carrier a)
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y))
     (and
      (q1038716-member-p
       carrier (q1038716-binary-value add x y))
      (q1038716-member-p
       carrier (q1038716-unary-value negate x))
      (q1038716-member-p
       carrier
       (q1038716-binary-value scalar-multiply a x))))))

(defun-sk q1038716-space-additive-laws-p
    (carrier add negate zero)
  (forall (x y z)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y)
      (q1038716-member-p carrier z))
     (and
      (equal
       (q1038716-binary-value
        add (q1038716-binary-value add x y) z)
       (q1038716-binary-value
        add x (q1038716-binary-value add y z)))
      (equal
       (q1038716-binary-value add x y)
       (q1038716-binary-value add y x))
      (equal (q1038716-binary-value add x zero) x)
      (equal
       (q1038716-binary-value
        add x (q1038716-unary-value negate x))
       zero)))))

(defun-sk q1038716-space-module-laws-p
    (field-carrier field-zero field-one field-add field-multiply
     carrier zero add scalar-multiply)
  (forall (a b x y)
    (implies
     (and
      (q1038716-member-p field-carrier a)
      (q1038716-member-p field-carrier b)
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y))
     (and
      (equal
       (q1038716-binary-value scalar-multiply field-one x)
       x)
      (equal
       (q1038716-binary-value
        scalar-multiply
        (q1038716-binary-value field-multiply a b)
        x)
       (q1038716-binary-value
        scalar-multiply a
        (q1038716-binary-value scalar-multiply b x)))
      (equal
       (q1038716-binary-value
        scalar-multiply
        (q1038716-binary-value field-add a b)
        x)
       (q1038716-binary-value
        add
        (q1038716-binary-value scalar-multiply a x)
        (q1038716-binary-value scalar-multiply b x)))
      (equal
       (q1038716-binary-value
        scalar-multiply a
        (q1038716-binary-value add x y))
       (q1038716-binary-value
        add
        (q1038716-binary-value scalar-multiply a x)
        (q1038716-binary-value scalar-multiply a y)))
      (equal
       (q1038716-binary-value scalar-multiply field-zero x)
       zero)
      (equal
       (q1038716-binary-value scalar-multiply a zero)
       zero)))))

(defun-sk q1038716-space-norm-negate-p
    (carrier negate norm)
  (forall (x q)
    (implies
     (q1038716-member-p carrier x)
     (iff
      (q1038716-norm-lt-p
       norm (q1038716-unary-value negate x) q)
      (q1038716-norm-lt-p norm x q)))))

(defun-sk q1038716-space-norm-add-p
    (carrier add norm)
  (forall (x y r s)
    (implies
     (and
      (q1038716-member-p carrier x)
      (q1038716-member-p carrier y)
      (q1038716-positive-rational-p r)
      (q1038716-positive-rational-p s)
      (q1038716-norm-lt-p norm x r)
      (q1038716-norm-lt-p norm y s))
     (q1038716-norm-lt-p
      norm (q1038716-binary-value add x y) (+ r s)))))

(defun-sk q1038716-space-norm-smul-p
    (field-carrier field-norm carrier scalar-multiply norm)
  (forall (a x q)
    (implies
     (and
      (q1038716-member-p field-carrier a)
      (q1038716-member-p carrier x))
     (iff
      (q1038716-norm-lt-p
       norm (q1038716-binary-value scalar-multiply a x) q)
      (q1038716-norm-product-lt-p
       field-norm norm a x q)))))

(defun q1038716-normed-space-p
    (field-carrier field-zero field-one field-add field-multiply
     field-norm carrier zero add negate scalar-multiply norm)
  (and
   (q1038716-member-p carrier zero)
   (q1038716-space-closure-p
    field-carrier carrier add negate scalar-multiply)
   (q1038716-space-additive-laws-p carrier add negate zero)
   (q1038716-space-module-laws-p
    field-carrier field-zero field-one field-add field-multiply
    carrier zero add scalar-multiply)
   (q1038716-norm-cut-laws-p carrier norm zero)
   (q1038716-space-norm-negate-p carrier negate norm)
   (q1038716-space-norm-add-p carrier add norm)
   (q1038716-space-norm-smul-p
    field-carrier field-norm carrier scalar-multiply norm)))

(defun q1038716-field-difference (add negate left right)
  (q1038716-binary-value
   add left (q1038716-unary-value negate right)))

(defun q1038716-space-difference (add negate left right)
  (q1038716-binary-value
   add left (q1038716-unary-value negate right)))

;; Arbitrary subsets, functions, and coefficient sequences.

(defun-sk q1038716-valid-set-p (field-carrier set)
  (forall (x)
    (implies
     (q1038716-member-p set x)
     (q1038716-member-p field-carrier x))))

(defun-sk q1038716-function-p
    (field-carrier space-carrier function)
  (forall (x)
    (implies
     (q1038716-member-p field-carrier x)
     (q1038716-member-p
      space-carrier (q1038716-unary-value function x)))))

(defun-sk q1038716-coefficient-sequence-p
    (space-carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (q1038716-member-p
      space-carrier (q1038716-unary-value sequence n)))))

;; Scalar powers, vector-valued power-series partial sums, and convergence.

(defun q1038716-field-power (one multiply base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (q1038716-binary-value
     multiply
     base
     (q1038716-field-power
      one multiply base (1- exponent)))))

(defun q1038716-power-series-partial-sum
    (field-one field-multiply space-zero space-add scalar-multiply
     coefficients delta count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      space-zero
    (let ((index (1- count)))
      (q1038716-binary-value
       space-add
       (q1038716-power-series-partial-sum
        field-one field-multiply space-zero space-add scalar-multiply
        coefficients delta index)
       (q1038716-binary-value
        scalar-multiply
        (q1038716-field-power
         field-one field-multiply delta index)
        (q1038716-unary-value coefficients index))))))

(defun-sk q1038716-convergence-tail-p
    (field-one field-multiply space-zero space-add space-negate
     scalar-multiply space-norm coefficients delta limit
     epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (q1038716-norm-lt-p
      space-norm
      (q1038716-space-difference
       space-add space-negate
       (q1038716-power-series-partial-sum
        field-one field-multiply space-zero space-add scalar-multiply
        coefficients delta count)
       limit)
      epsilon))))

(defun-sk q1038716-convergence-cutoff-exists-p
    (field-one field-multiply space-zero space-add space-negate
     scalar-multiply space-norm coefficients delta limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1038716-convergence-tail-p
      field-one field-multiply space-zero space-add space-negate
      scalar-multiply space-norm coefficients delta limit
      epsilon cutoff))))

(defun-sk q1038716-power-series-converges-p
    (field-one field-multiply space-zero space-add space-negate
     scalar-multiply space-norm coefficients delta limit)
  (forall (epsilon)
    (implies
     (q1038716-positive-rational-p epsilon)
     (q1038716-convergence-cutoff-exists-p
      field-one field-multiply space-zero space-add space-negate
      scalar-multiply space-norm coefficients delta limit epsilon))))

;; Analyticity is local representability by a convergent scalar power series.
;; For a one-dimensional field domain, continuous multilinear coefficients are
;; equivalently their values at (1,...,1), hence the vector coefficient
;; sequence below is definitionally equivalent to the source power series.

(defun-sk q1038716-power-series-ball-p
    (field-carrier field-one field-add field-multiply field-negate
     field-norm space-zero space-add space-negate scalar-multiply
     space-norm function center coefficients radius)
  (forall (z)
    (implies
     (and
      (q1038716-member-p field-carrier z)
      (q1038716-norm-lt-p
       field-norm
       (q1038716-field-difference field-add field-negate z center)
       radius))
     (q1038716-power-series-converges-p
      field-one field-multiply space-zero space-add space-negate
      scalar-multiply space-norm coefficients
      (q1038716-field-difference field-add field-negate z center)
      (q1038716-unary-value function z)))))

(defun q1038716-analytic-witness-p
    (field-carrier field-one field-add field-multiply field-negate
     field-norm space-carrier space-zero space-add space-negate
     scalar-multiply space-norm function center coefficients radius)
  (and
   (q1038716-coefficient-sequence-p space-carrier coefficients)
   (q1038716-positive-rational-p radius)
   (q1038716-power-series-ball-p
    field-carrier field-one field-add field-multiply field-negate
    field-norm space-zero space-add space-negate scalar-multiply
    space-norm function center coefficients radius)))

(defun-sk q1038716-analytic-at-p
    (field-carrier field-one field-add field-multiply field-negate
     field-norm space-carrier space-zero space-add space-negate
     scalar-multiply space-norm function center)
  (exists (coefficients radius)
    (q1038716-analytic-witness-p
     field-carrier field-one field-add field-multiply field-negate
     field-norm space-carrier space-zero space-add space-negate
     scalar-multiply space-norm function center coefficients radius)))

(defun-sk q1038716-analytic-on-neighborhood-p
    (field-carrier field-one field-add field-multiply field-negate
     field-norm space-carrier space-zero space-add space-negate
     scalar-multiply space-norm function set)
  (forall (center)
    (implies
     (q1038716-member-p set center)
     (q1038716-analytic-at-p
      field-carrier field-one field-add field-multiply field-negate
      field-norm space-carrier space-zero space-add space-negate
      scalar-multiply space-norm function center))))

;; The norm topology and preconnectedness.

(defun-sk q1038716-open-ball-contained-p
    (field-carrier field-add field-negate field-norm
     set center radius)
  (forall (point)
    (implies
     (and
      (q1038716-member-p field-carrier point)
      (q1038716-norm-lt-p
       field-norm
       (q1038716-field-difference
        field-add field-negate point center)
       radius))
     (q1038716-member-p set point))))

(defun-sk q1038716-open-radius-exists-p
    (field-carrier field-add field-negate field-norm set center)
  (exists (radius)
    (and
     (q1038716-positive-rational-p radius)
     (q1038716-open-ball-contained-p
      field-carrier field-add field-negate field-norm
      set center radius))))

(defun-sk q1038716-metric-open-p
    (field-carrier field-add field-negate field-norm set)
  (forall (center)
    (implies
     (q1038716-member-p set center)
     (q1038716-open-radius-exists-p
      field-carrier field-add field-negate field-norm
      set center))))

(defun-sk q1038716-cover-p (set left right)
  (forall (x)
    (implies
     (q1038716-member-p set x)
     (or
      (q1038716-member-p left x)
      (q1038716-member-p right x)))))

(defun-sk q1038716-intersects-p (left right)
  (exists (x)
    (and
     (q1038716-member-p left x)
     (q1038716-member-p right x))))

(defun-sk q1038716-triple-intersects-p (set left right)
  (exists (x)
    (and
     (q1038716-member-p set x)
     (q1038716-member-p left x)
     (q1038716-member-p right x))))

(defun-sk q1038716-preconnected-p
    (field-carrier field-add field-negate field-norm set)
  (forall (left right)
    (implies
     (and
      (q1038716-valid-set-p field-carrier left)
      (q1038716-valid-set-p field-carrier right)
      (q1038716-metric-open-p
       field-carrier field-add field-negate field-norm left)
      (q1038716-metric-open-p
       field-carrier field-add field-negate field-norm right)
      (q1038716-cover-p set left right)
      (q1038716-intersects-p set left)
      (q1038716-intersects-p set right))
     (q1038716-triple-intersects-p set left right))))

;; Frequent equality in the punctured neighborhood filter and equality on U.

(defun-sk q1038716-frequent-equality-witness-exists-p
    (field-carrier field-add field-negate field-norm
     function-g function-h center radius)
  (exists (z)
    (and
     (q1038716-member-p field-carrier z)
     (not (equal z center))
     (q1038716-norm-lt-p
      field-norm
      (q1038716-field-difference
       field-add field-negate z center)
      radius)
     (equal
      (q1038716-unary-value function-g z)
      (q1038716-unary-value function-h z)))))

(defun-sk q1038716-frequently-equal-off-p
    (field-carrier field-add field-negate field-norm
     function-g function-h center)
  (forall (radius)
    (implies
     (q1038716-positive-rational-p radius)
     (q1038716-frequent-equality-witness-exists-p
      field-carrier field-add field-negate field-norm
      function-g function-h center radius))))

(defun-sk q1038716-equal-on-p (set function-g function-h)
  (forall (z)
    (implies
     (q1038716-member-p set z)
     (equal
      (q1038716-unary-value function-g z)
      (q1038716-unary-value function-h z)))))

(defun-sk thousand-theorems-q1038716-identity-theorem-statement ()
  (forall
    (field-carrier field-zero field-one field-add field-multiply
     field-negate field-inverse field-norm
     space-carrier space-zero space-add space-negate
     scalar-multiply space-norm set function-g function-h center)
    (implies
     (and
      (q1038716-nontrivially-normed-field-p
       field-carrier field-zero field-one field-add field-multiply
       field-negate field-inverse field-norm)
      (q1038716-normed-space-p
       field-carrier field-zero field-one field-add field-multiply
       field-norm space-carrier space-zero space-add space-negate
       scalar-multiply space-norm)
      (q1038716-valid-set-p field-carrier set)
      (q1038716-function-p
       field-carrier space-carrier function-g)
      (q1038716-function-p
       field-carrier space-carrier function-h)
      (q1038716-analytic-on-neighborhood-p
       field-carrier field-one field-add field-multiply field-negate
       field-norm space-carrier space-zero space-add space-negate
       scalar-multiply space-norm function-g set)
      (q1038716-analytic-on-neighborhood-p
       field-carrier field-one field-add field-multiply field-negate
       field-norm space-carrier space-zero space-add space-negate
       scalar-multiply space-norm function-h set)
      (q1038716-preconnected-p
       field-carrier field-add field-negate field-norm set)
      (q1038716-member-p set center)
      (q1038716-frequently-equal-off-p
       field-carrier field-add field-negate field-norm
       function-g function-h center))
     (q1038716-equal-on-p set function-g function-h))))

(value-triple :itpeval-statement-checked)
:q
