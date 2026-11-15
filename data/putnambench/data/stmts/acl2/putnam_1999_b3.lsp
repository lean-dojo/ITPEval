;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_b3:
;; the two-variable boundary limit of an iterated real power series over
;; positive integer pairs whose coordinate ratio lies between 1/2 and 2.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers up to their
;; unique ordered-field isomorphism. Tame APPLY$ function objects retain the
;; arbitrary real-valued function S and arbitrary subsets used by
;; completeness; DEFUN-SK supplies all unbounded quantifiers.

(defun p99b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p99b3-unary-value (operation x)
  (apply$ operation (list x)))

(defun p99b3-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p99b3-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p99b3-member-p carrier x))))

(defun-sk p99b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p99b3-member-p carrier x)
      (p99b3-member-p carrier y)
      (p99b3-member-p carrier z))
     (and
      (p99b3-member-p carrier
                      (p99b3-binary-value add x y))
      (p99b3-member-p carrier
                      (p99b3-binary-value multiply x y))
      (p99b3-member-p carrier
                      (p99b3-unary-value negate x))
      (p99b3-member-p carrier
                      (p99b3-unary-value inverse x))
      (equal
       (p99b3-binary-value
        add (p99b3-binary-value add x y) z)
       (p99b3-binary-value
        add x (p99b3-binary-value add y z)))
      (equal
       (p99b3-binary-value add x y)
       (p99b3-binary-value add y x))
      (equal (p99b3-binary-value add x zero) x)
      (equal
       (p99b3-binary-value
        add x (p99b3-unary-value negate x))
       zero)
      (equal
       (p99b3-binary-value
        multiply (p99b3-binary-value multiply x y) z)
       (p99b3-binary-value
        multiply x (p99b3-binary-value multiply y z)))
      (equal
       (p99b3-binary-value multiply x y)
       (p99b3-binary-value multiply y x))
      (equal (p99b3-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p99b3-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p99b3-binary-value
         multiply x (p99b3-unary-value inverse x))
        one))
      (equal
       (p99b3-binary-value
        multiply x (p99b3-binary-value add y z))
       (p99b3-binary-value
        add
        (p99b3-binary-value multiply x y)
        (p99b3-binary-value multiply x z)))))))

(defun-sk p99b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p99b3-member-p carrier x)
      (p99b3-member-p carrier y)
      (p99b3-member-p carrier z))
     (and
      (not (p99b3-binary-value less x x))
      (or
       (equal x y)
       (p99b3-binary-value less x y)
       (p99b3-binary-value less y x))
      (implies
       (and
        (p99b3-binary-value less x y)
        (p99b3-binary-value less y z))
       (p99b3-binary-value less x z))
      (implies
       (p99b3-binary-value less x y)
       (p99b3-binary-value
        less
        (p99b3-binary-value add x z)
        (p99b3-binary-value add y z)))
      (implies
       (and
        (p99b3-binary-value less zero x)
        (p99b3-binary-value less zero y))
       (p99b3-binary-value
        less
        zero
        (p99b3-binary-value multiply x y)))))))

(defun-sk p99b3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p99b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p99b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p99b3-member-p carrier x)
      (apply$ set (list x)))
     (not (p99b3-binary-value less bound x)))))

(defun-sk p99b3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p99b3-member-p carrier bound)
     (p99b3-upper-bound-p
      carrier less set bound))))

(defun-sk p99b3-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p99b3-member-p carrier bound)
      (p99b3-upper-bound-p carrier less set bound))
     (not
      (p99b3-binary-value less bound supremum)))))

(defun p99b3-supremum-p
    (carrier less set supremum)
  (and
   (p99b3-member-p carrier supremum)
   (p99b3-upper-bound-p carrier less set supremum)
   (p99b3-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p99b3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p99b3-supremum-p
     carrier less set supremum)))

(defun-sk p99b3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p99b3-valid-set-p carrier set)
      (p99b3-set-nonempty-p carrier set)
      (p99b3-bounded-above-p carrier less set))
     (p99b3-has-supremum-p
      carrier less set))))

(defun p99b3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p99b3-member-p carrier zero)
   (p99b3-member-p carrier one)
   (not (equal zero one))
   (p99b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p99b3-order-laws-p
    carrier add multiply zero less)
   (p99b3-binary-value less zero one)
   (p99b3-dedekind-complete-p carrier less)))

;; The context is
;; (carrier zero one add multiply negate inverse less).

(defun p99b3-r-carrier (ctx) (nth 0 ctx))
(defun p99b3-r-zero (ctx) (nth 1 ctx))
(defun p99b3-r-one (ctx) (nth 2 ctx))
(defun p99b3-r-add (ctx) (nth 3 ctx))
(defun p99b3-r-mul (ctx) (nth 4 ctx))
(defun p99b3-r-neg (ctx) (nth 5 ctx))
(defun p99b3-r-inv (ctx) (nth 6 ctx))
(defun p99b3-r-lt (ctx) (nth 7 ctx))

(defun p99b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p99b3-real-field-p
    (p99b3-r-carrier ctx)
    (p99b3-r-zero ctx)
    (p99b3-r-one ctx)
    (p99b3-r-add ctx)
    (p99b3-r-mul ctx)
    (p99b3-r-neg ctx)
    (p99b3-r-inv ctx)
    (p99b3-r-lt ctx))))

(defun p99b3-r-add-value (ctx x y)
  (p99b3-binary-value (p99b3-r-add ctx) x y))

(defun p99b3-r-mul-value (ctx x y)
  (p99b3-binary-value (p99b3-r-mul ctx) x y))

(defun p99b3-r-neg-value (ctx x)
  (p99b3-unary-value (p99b3-r-neg ctx) x))

(defun p99b3-r-sub-value (ctx x y)
  (p99b3-r-add-value
   ctx x (p99b3-r-neg-value ctx y)))

(defun p99b3-r-lt-p (ctx x y)
  (if (p99b3-binary-value (p99b3-r-lt ctx) x y)
      t nil))

(defun p99b3-r-le-p (ctx x y)
  (not (p99b3-r-lt-p ctx y x)))

(defun p99b3-r-abs-value (ctx x)
  (if (p99b3-r-lt-p ctx x (p99b3-r-zero ctx))
      (p99b3-r-neg-value ctx x)
    x))

(defun p99b3-positive-real-p (ctx x)
  (and
   (p99b3-member-p (p99b3-r-carrier ctx) x)
   (p99b3-r-lt-p ctx (p99b3-r-zero ctx) x)))

(defun p99b3-three (ctx)
  (p99b3-r-add-value
   ctx
   (p99b3-r-one ctx)
   (p99b3-r-add-value
    ctx
    (p99b3-r-one ctx)
    (p99b3-r-one ctx))))

(defun p99b3-r-power (ctx base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p99b3-r-one ctx)
    (p99b3-r-mul-value
     ctx
     base
     (p99b3-r-power ctx base (1- exponent)))))

;; For positive M and N, N <= 2*M and M <= 2*N are exactly the source
;; inequalities 1/2 <= M/N <= 2.

(defun p99b3-wedge-p (m n)
  (and
   (posp m)
   (posp n)
   (<= n (* 2 m))
   (<= m (* 2 n))))

(defun p99b3-term (ctx x y m n)
  (if (p99b3-wedge-p m n)
      (p99b3-r-mul-value
       ctx
       (p99b3-r-power ctx x m)
       (p99b3-r-power ctx y n))
    (p99b3-r-zero ctx)))

(defun p99b3-row-prefix (ctx x y m count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p99b3-r-zero ctx)
    (p99b3-r-add-value
     ctx
     (p99b3-row-prefix ctx x y m (1- count))
     (p99b3-term ctx x y m count))))

(defun-sk p99b3-row-convergence-tail-p
    (ctx x y m limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (p99b3-r-lt-p
      ctx
      (p99b3-r-abs-value
       ctx
       (p99b3-r-sub-value
        ctx
        (p99b3-row-prefix ctx x y m count)
        limit))
      epsilon))))

(defun-sk p99b3-row-cutoff-exists-p
    (ctx x y m limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p99b3-row-convergence-tail-p
      ctx x y m limit epsilon cutoff))))

(defun-sk p99b3-row-sums-to-p
    (ctx x y m limit)
  (forall (epsilon)
    (implies
     (p99b3-positive-real-p ctx epsilon)
     (p99b3-row-cutoff-exists-p
      ctx x y m limit epsilon))))

(defun-sk p99b3-row-summable-p
    (ctx x y m)
  (exists (limit)
    (and
     (p99b3-member-p (p99b3-r-carrier ctx) limit)
     (p99b3-row-sums-to-p
      ctx x y m limit))))

;; This is the standard totalized infinite-sum convention: a convergent row
;; has its unique limit, and a non-summable row has value zero.

(defun p99b3-row-tsum-p
    (ctx x y m value)
  (and
   (p99b3-member-p (p99b3-r-carrier ctx) value)
   (if (p99b3-row-summable-p ctx x y m)
       (p99b3-row-sums-to-p ctx x y m value)
     (equal value (p99b3-r-zero ctx)))))

(defun-sk p99b3-row-tsums-values-p
    (ctx x y row-tsums)
  (forall (m)
    (implies
     (natp m)
     (p99b3-row-tsum-p
      ctx x y m (apply$ row-tsums (list m))))))

(defun p99b3-row-tsums-function-p
    (ctx x y row-tsums)
  (and
   (tamep-functionp row-tsums)
   (p99b3-row-tsums-values-p
    ctx x y row-tsums)))

(defun p99b3-outer-prefix
    (ctx row-tsums count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p99b3-r-zero ctx)
    (p99b3-r-add-value
     ctx
     (p99b3-outer-prefix
      ctx row-tsums (1- count))
     (apply$ row-tsums (list count)))))

(defun-sk p99b3-outer-convergence-tail-p
    (ctx row-tsums limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (p99b3-r-lt-p
      ctx
      (p99b3-r-abs-value
       ctx
       (p99b3-r-sub-value
        ctx
        (p99b3-outer-prefix ctx row-tsums count)
        limit))
      epsilon))))

(defun-sk p99b3-outer-cutoff-exists-p
    (ctx row-tsums limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p99b3-outer-convergence-tail-p
      ctx row-tsums limit epsilon cutoff))))

(defun-sk p99b3-outer-sums-to-p
    (ctx row-tsums limit)
  (forall (epsilon)
    (implies
     (p99b3-positive-real-p ctx epsilon)
     (p99b3-outer-cutoff-exists-p
      ctx row-tsums limit epsilon))))

(defun-sk p99b3-outer-summable-p
    (ctx row-tsums)
  (exists (limit)
    (and
     (p99b3-member-p (p99b3-r-carrier ctx) limit)
     (p99b3-outer-sums-to-p
      ctx row-tsums limit))))

;; The existential row-tsums function keeps the inner-sum witnesses internal.
;; The outer totalization then represents exactly Sum_m (Sum_n term(m,n)).

(defun-sk p99b3-iterated-tsum-p
    (ctx x y total)
  (exists (row-tsums)
    (and
     (p99b3-row-tsums-function-p
      ctx x y row-tsums)
     (if (p99b3-outer-summable-p ctx row-tsums)
         (p99b3-outer-sums-to-p
          ctx row-tsums total)
       (equal total (p99b3-r-zero ctx))))))

(defun p99b3-series-value (series x y)
  (apply$ series (list x y)))

(defun-sk p99b3-series-definition-p
    (ctx series)
  (forall (x y)
    (implies
     (and
      (p99b3-member-p (p99b3-r-carrier ctx) x)
      (p99b3-member-p (p99b3-r-carrier ctx) y))
     (let ((value (p99b3-series-value series x y)))
       (and
        (p99b3-member-p
         (p99b3-r-carrier ctx) value)
        (p99b3-iterated-tsum-p
         ctx x y value))))))

(defun p99b3-in-source-domain-p (ctx x y)
  (and
   (p99b3-member-p (p99b3-r-carrier ctx) x)
   (p99b3-member-p (p99b3-r-carrier ctx) y)
   (p99b3-r-le-p ctx (p99b3-r-zero ctx) x)
   (p99b3-r-lt-p ctx x (p99b3-r-one ctx))
   (p99b3-r-le-p ctx (p99b3-r-zero ctx) y)
   (p99b3-r-lt-p ctx y (p99b3-r-one ctx))))

(defun p99b3-normalized-value
    (ctx series x y)
  (let* ((one (p99b3-r-one ctx))
         (x-y-squared
          (p99b3-r-mul-value
           ctx x (p99b3-r-power ctx y 2)))
         (x-squared-y
          (p99b3-r-mul-value
           ctx (p99b3-r-power ctx x 2) y)))
    (p99b3-r-mul-value
     ctx
     (p99b3-r-sub-value ctx one x-y-squared)
     (p99b3-r-mul-value
      ctx
      (p99b3-r-sub-value ctx one x-squared-y)
      (p99b3-series-value series x y)))))

;; Coordinatewise neighborhoods give the product topology on R x R, so this
;; epsilon-delta predicate is equivalent to the source filter limit within A.

(defun-sk p99b3-limit-neighborhood-p
    (ctx series epsilon delta)
  (forall (x y)
    (implies
     (and
      (p99b3-in-source-domain-p ctx x y)
      (p99b3-r-lt-p
       ctx
       (p99b3-r-abs-value
        ctx
        (p99b3-r-sub-value
         ctx x (p99b3-r-one ctx)))
       delta)
      (p99b3-r-lt-p
       ctx
       (p99b3-r-abs-value
        ctx
        (p99b3-r-sub-value
         ctx y (p99b3-r-one ctx)))
       delta))
     (p99b3-r-lt-p
      ctx
      (p99b3-r-abs-value
       ctx
       (p99b3-r-sub-value
        ctx
        (p99b3-normalized-value
         ctx series x y)
        (p99b3-three ctx)))
      epsilon))))

(defun-sk p99b3-limit-delta-exists-p
    (ctx series epsilon)
  (exists (delta)
    (and
     (p99b3-positive-real-p ctx delta)
     (p99b3-limit-neighborhood-p
      ctx series epsilon delta))))

(defun-sk p99b3-limit-is-three-p
    (ctx series)
  (forall (epsilon)
    (implies
     (p99b3-positive-real-p ctx epsilon)
     (p99b3-limit-delta-exists-p
      ctx series epsilon))))

(defun putnambench-putnam-1999-b3-statement
    (ctx series)
  (implies
   (and
    (p99b3-context-p ctx)
    (tamep-functionp series)
    (p99b3-series-definition-p ctx series))
   (p99b3-limit-is-three-p ctx series)))

(value-triple :itpeval-statement-checked)
:q
