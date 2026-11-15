;; Statement-only formalization of PutnamBench artifact putnam_1962_b6:
;; a nonconstant real trigonometric polynomial bounded by one and attaining
;; absolute value one at 2n distinct points is a phase shift of its
;; top-degree cosine. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has no primitive real sort.  The context below presents an
;; arbitrary Dedekind-complete ordered field, hence the real field up to its
;; unique ordered-field isomorphism.  Sine, cosine, and pi are defined by their
;; convergent rational power series (and the Leibniz series for pi), rather
;; than supplied as certificate hypotheses.  DEFUN-SK keeps every analytic
;; quantifier and the conclusion's phase witness internal to the statement.
;;
;; Only a_0,...,a_n and b_0,...,b_n occur in the source polynomial, so finite
;; lists of length n+1 are definitionally equivalent to those initial
;; coefficient segments; arbitrary real entries, including transcendental
;; ones, remain allowed.  Likewise, a duplicate-free list of length 2n exactly
;; enumerates the source's finite set of extremal points.

(defun p62b6-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p62b6-unary (operation x)
  (apply$ operation (list x)))

(defun p62b6-binary (operation x y)
  (apply$ operation (list x y)))

(defun-sk p62b6-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (p62b6-member-p carrier x)
          (p62b6-member-p carrier y)
          (p62b6-member-p carrier z))
     (and
      (p62b6-member-p carrier (p62b6-binary add x y))
      (p62b6-member-p carrier (p62b6-binary multiply x y))
      (p62b6-member-p carrier (p62b6-unary negate x))
      (p62b6-member-p carrier (p62b6-unary inverse x))
      (equal
       (p62b6-binary add (p62b6-binary add x y) z)
       (p62b6-binary add x (p62b6-binary add y z)))
      (equal (p62b6-binary add x y)
             (p62b6-binary add y x))
      (equal (p62b6-binary add x zero) x)
      (equal
       (p62b6-binary add x (p62b6-unary negate x))
       zero)
      (equal
       (p62b6-binary
        multiply (p62b6-binary multiply x y) z)
       (p62b6-binary
        multiply x (p62b6-binary multiply y z)))
      (equal (p62b6-binary multiply x y)
             (p62b6-binary multiply y x))
      (equal (p62b6-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (p62b6-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p62b6-binary multiply x (p62b6-unary inverse x))
        one))
      (equal
       (p62b6-binary multiply x (p62b6-binary add y z))
       (p62b6-binary
        add
        (p62b6-binary multiply x y)
        (p62b6-binary multiply x z)))))))

(defun-sk p62b6-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (p62b6-member-p carrier x)
          (p62b6-member-p carrier y)
          (p62b6-member-p carrier z))
     (and
      (not (p62b6-binary less x x))
      (or (equal x y)
          (p62b6-binary less x y)
          (p62b6-binary less y x))
      (implies
       (and (p62b6-binary less x y)
            (p62b6-binary less y z))
       (p62b6-binary less x z))
      (implies
       (p62b6-binary less x y)
       (p62b6-binary
        less
        (p62b6-binary add x z)
        (p62b6-binary add y z)))
      (implies
       (and (p62b6-binary less zero x)
            (p62b6-binary less zero y))
       (p62b6-binary
        less zero (p62b6-binary multiply x y)))))))

(defun-sk p62b6-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p62b6-member-p carrier x))))

(defun-sk p62b6-set-nonempty-p (carrier set)
  (exists (x)
    (and (p62b6-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk p62b6-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and (p62b6-member-p carrier x)
          (apply$ set (list x)))
     (not (p62b6-binary less bound x)))))

(defun-sk p62b6-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p62b6-member-p carrier bound)
     (p62b6-upper-bound-p carrier less set bound))))

(defun-sk p62b6-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p62b6-member-p carrier bound)
      (p62b6-upper-bound-p carrier less set bound))
     (not (p62b6-binary less bound supremum)))))

(defun p62b6-supremum-p
    (carrier less set supremum)
  (and
   (p62b6-member-p carrier supremum)
   (p62b6-upper-bound-p carrier less set supremum)
   (p62b6-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p62b6-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p62b6-supremum-p
     carrier less set supremum)))

(defun-sk p62b6-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p62b6-valid-set-p carrier set)
      (p62b6-set-nonempty-p carrier set)
      (p62b6-bounded-above-p carrier less set))
     (p62b6-has-supremum-p carrier less set))))

(defun p62b6-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p62b6-member-p carrier zero)
   (p62b6-member-p carrier one)
   (not (equal zero one))
   (p62b6-field-laws-p
    carrier add multiply negate inverse zero one)
   (p62b6-order-laws-p
    carrier add multiply zero less)
   (p62b6-binary less zero one)
   (p62b6-dedekind-complete-p carrier less)))

;; Real-field context and arithmetic.

(defun p62b6-r-carrier (ctx) (nth 0 ctx))
(defun p62b6-r-zero (ctx) (nth 1 ctx))
(defun p62b6-r-one (ctx) (nth 2 ctx))
(defun p62b6-r-add (ctx) (nth 3 ctx))
(defun p62b6-r-mul (ctx) (nth 4 ctx))
(defun p62b6-r-neg (ctx) (nth 5 ctx))
(defun p62b6-r-inv (ctx) (nth 6 ctx))
(defun p62b6-r-lt (ctx) (nth 7 ctx))

(defun p62b6-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p62b6-real-field-p
    (p62b6-r-carrier ctx)
    (p62b6-r-add ctx)
    (p62b6-r-mul ctx)
    (p62b6-r-neg ctx)
    (p62b6-r-inv ctx)
    (p62b6-r-zero ctx)
    (p62b6-r-one ctx)
    (p62b6-r-lt ctx))))

(defun p62b6-r-add-value (ctx x y)
  (p62b6-binary (p62b6-r-add ctx) x y))

(defun p62b6-r-mul-value (ctx x y)
  (p62b6-binary (p62b6-r-mul ctx) x y))

(defun p62b6-r-neg-value (ctx x)
  (p62b6-unary (p62b6-r-neg ctx) x))

(defun p62b6-r-inv-value (ctx x)
  (p62b6-unary (p62b6-r-inv ctx) x))

(defun p62b6-r-sub-value (ctx x y)
  (p62b6-r-add-value
   ctx x (p62b6-r-neg-value ctx y)))

(defun p62b6-r-div-value (ctx x y)
  (p62b6-r-mul-value
   ctx x (p62b6-r-inv-value ctx y)))

(defun p62b6-r-lt-p (ctx x y)
  (if (p62b6-binary (p62b6-r-lt ctx) x y) t nil))

(defun p62b6-r-le-p (ctx x y)
  (not (p62b6-r-lt-p ctx y x)))

(defun p62b6-r-abs-value (ctx x)
  (if (p62b6-r-lt-p ctx x (p62b6-r-zero ctx))
      (p62b6-r-neg-value ctx x)
    x))

(defun p62b6-positive-p (ctx x)
  (and
   (p62b6-member-p (p62b6-r-carrier ctx) x)
   (p62b6-r-lt-p ctx (p62b6-r-zero ctx) x)))

(defun p62b6-r-nat (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p62b6-r-zero ctx)
    (p62b6-r-add-value
     ctx
     (p62b6-r-one ctx)
     (p62b6-r-nat ctx (- n 1)))))

(defun p62b6-r-power (ctx x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p62b6-r-one ctx)
    (p62b6-r-mul-value
     ctx x (p62b6-r-power ctx x (- n 1)))))

(defun p62b6-r-factorial (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p62b6-r-one ctx)
    (p62b6-r-mul-value
     ctx
     (p62b6-r-nat ctx n)
     (p62b6-r-factorial ctx (- n 1)))))

(defun p62b6-alternating-sign (ctx n)
  (if (evenp n)
      (p62b6-r-one ctx)
    (p62b6-r-neg-value ctx (p62b6-r-one ctx))))

;; Exact sine and cosine values via their power series.

(defun p62b6-trig-term (ctx sinep x index)
  (let* ((exponent
          (if sinep (+ (* 2 index) 1) (* 2 index)))
         (numerator
          (p62b6-r-mul-value
           ctx
           (p62b6-alternating-sign ctx index)
           (p62b6-r-power ctx x exponent)))
         (denominator
          (p62b6-r-factorial ctx exponent)))
    (p62b6-r-div-value ctx numerator denominator)))

(defun p62b6-trig-prefix (ctx sinep x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p62b6-r-zero ctx)
    (let ((index (- terms 1)))
      (p62b6-r-add-value
       ctx
       (p62b6-trig-prefix ctx sinep x index)
       (p62b6-trig-term ctx sinep x index)))))

(defun-sk p62b6-trig-tail-p
    (ctx sinep x limit epsilon cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= cutoff terms))
     (p62b6-r-lt-p
      ctx
      (p62b6-r-abs-value
       ctx
       (p62b6-r-sub-value
        ctx
        (p62b6-trig-prefix ctx sinep x terms)
        limit))
      epsilon))))

(defun-sk p62b6-trig-cutoff-exists-p
    (ctx sinep x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p62b6-trig-tail-p
      ctx sinep x limit epsilon cutoff))))

(defun-sk p62b6-trig-value-p
    (ctx sinep x limit)
  (forall (epsilon)
    (implies
     (p62b6-positive-p ctx epsilon)
     (p62b6-trig-cutoff-exists-p
      ctx sinep x limit epsilon))))

(defun p62b6-sine-value-p (ctx x value)
  (and
   (p62b6-member-p (p62b6-r-carrier ctx) x)
   (p62b6-member-p (p62b6-r-carrier ctx) value)
   (p62b6-trig-value-p ctx t x value)))

(defun p62b6-cosine-value-p (ctx x value)
  (and
   (p62b6-member-p (p62b6-r-carrier ctx) x)
   (p62b6-member-p (p62b6-r-carrier ctx) value)
   (p62b6-trig-value-p ctx nil x value)))

;; pi = 4 * sum_{j >= 0} (-1)^j/(2j+1).

(defun p62b6-leibniz-term (ctx index)
  (p62b6-r-div-value
   ctx
   (p62b6-alternating-sign ctx index)
   (p62b6-r-nat ctx (+ (* 2 index) 1))))

(defun p62b6-leibniz-prefix (ctx terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p62b6-r-zero ctx)
    (let ((index (- terms 1)))
      (p62b6-r-add-value
       ctx
       (p62b6-leibniz-prefix ctx index)
       (p62b6-leibniz-term ctx index)))))

(defun p62b6-pi-prefix (ctx terms)
  (p62b6-r-mul-value
   ctx
   (p62b6-r-nat ctx 4)
   (p62b6-leibniz-prefix ctx terms)))

(defun-sk p62b6-pi-tail-p
    (ctx pi-value epsilon cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= cutoff terms))
     (p62b6-r-lt-p
      ctx
      (p62b6-r-abs-value
       ctx
       (p62b6-r-sub-value
        ctx (p62b6-pi-prefix ctx terms) pi-value))
      epsilon))))

(defun-sk p62b6-pi-cutoff-exists-p
    (ctx pi-value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p62b6-pi-tail-p ctx pi-value epsilon cutoff))))

(defun-sk p62b6-pi-value-p (ctx pi-value)
  (forall (epsilon)
    (implies
     (p62b6-positive-p ctx epsilon)
     (p62b6-pi-cutoff-exists-p
      ctx pi-value epsilon))))

;; Coefficients and the finite trigonometric sum.

(defun p62b6-real-list-p (ctx values)
  (if (consp values)
      (and
       (p62b6-member-p
        (p62b6-r-carrier ctx) (car values))
       (p62b6-real-list-p ctx (cdr values)))
    (equal values nil)))

(defun p62b6-trig-witness-lists-p
    (ctx x sines cosines index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (and (endp sines) (endp cosines))
    (and
     (consp sines)
     (consp cosines)
     (let ((argument
            (p62b6-r-mul-value
             ctx (p62b6-r-nat ctx index) x)))
       (and
        (p62b6-sine-value-p ctx argument (car sines))
        (p62b6-cosine-value-p ctx argument (car cosines))))
     (p62b6-trig-witness-lists-p
      ctx x (cdr sines) (cdr cosines)
      (+ index 1) (- remaining 1)))))

(defun p62b6-weighted-sum
    (ctx a b sines cosines)
  (if (and (consp a)
           (consp b)
           (consp sines)
           (consp cosines))
      (p62b6-r-add-value
       ctx
       (p62b6-r-add-value
        ctx
        (p62b6-r-mul-value
         ctx (car a) (car sines))
        (p62b6-r-mul-value
         ctx (car b) (car cosines)))
       (p62b6-weighted-sum
        ctx (cdr a) (cdr b)
        (cdr sines) (cdr cosines)))
    (p62b6-r-zero ctx)))

(defun-sk p62b6-polynomial-value-p
    (ctx n a b x value)
  (exists (sines cosines)
    (and
     (p62b6-member-p (p62b6-r-carrier ctx) x)
     (p62b6-member-p (p62b6-r-carrier ctx) value)
     (p62b6-trig-witness-lists-p
      ctx x sines cosines 0 (+ n 1))
     (equal
      value
      (p62b6-weighted-sum
       ctx a b sines cosines)))))

(defun p62b6-in-closed-period-p (ctx pi-value x)
  (and
   (p62b6-member-p (p62b6-r-carrier ctx) x)
   (p62b6-r-le-p ctx (p62b6-r-zero ctx) x)
   (p62b6-r-le-p
    ctx x
    (p62b6-r-mul-value
     ctx (p62b6-r-nat ctx 2) pi-value))))

(defun p62b6-in-half-open-period-p (ctx pi-value x)
  (and
   (p62b6-member-p (p62b6-r-carrier ctx) x)
   (p62b6-r-le-p ctx (p62b6-r-zero ctx) x)
   (p62b6-r-lt-p
    ctx x
    (p62b6-r-mul-value
     ctx (p62b6-r-nat ctx 2) pi-value))))

(defun-sk p62b6-bounded-at-point-p
    (ctx n a b x)
  (exists (value)
    (and
     (p62b6-polynomial-value-p
      ctx n a b x value)
     (p62b6-r-le-p
      ctx
      (p62b6-r-abs-value ctx value)
      (p62b6-r-one ctx)))))

(defun-sk p62b6-global-bound-p
    (ctx n a b pi-value)
  (forall (x)
    (implies
     (p62b6-in-closed-period-p ctx pi-value x)
     (p62b6-bounded-at-point-p
      ctx n a b x))))

(defun-sk p62b6-extreme-point-p
    (ctx n a b pi-value x)
  (exists (value)
    (and
     (p62b6-in-half-open-period-p ctx pi-value x)
     (p62b6-polynomial-value-p
      ctx n a b x value)
     (equal
      (p62b6-r-abs-value ctx value)
      (p62b6-r-one ctx)))))

(defun p62b6-extreme-point-list-p
    (ctx n a b pi-value points)
  (if (consp points)
      (and
       (p62b6-extreme-point-p
        ctx n a b pi-value (car points))
       (p62b6-extreme-point-list-p
        ctx n a b pi-value (cdr points)))
    (equal points nil)))

(defun-sk p62b6-source-hypotheses-p
    (ctx n a b points)
  (exists (pi-value)
    (and
     (p62b6-member-p (p62b6-r-carrier ctx) pi-value)
     (p62b6-pi-value-p ctx pi-value)
     (p62b6-global-bound-p ctx n a b pi-value)
     (true-listp points)
     (equal (len points) (* 2 n))
     (no-duplicatesp-equal points)
     (p62b6-extreme-point-list-p
      ctx n a b pi-value points))))

;; The source's nonconstant premise and phase-shift conclusion, with all
;; witnesses and pointwise function equalities kept internal.

(defun-sk p62b6-value-equals-p
    (ctx n a b x expected)
  (exists (value)
    (and
     (p62b6-polynomial-value-p
      ctx n a b x value)
     (equal value expected))))

(defun-sk p62b6-constant-value-p
    (ctx n a b constant)
  (forall (x)
    (implies
     (p62b6-member-p (p62b6-r-carrier ctx) x)
     (p62b6-value-equals-p
      ctx n a b x constant))))

(defun-sk p62b6-constant-exists-p
    (ctx n a b)
  (exists (constant)
    (and
     (p62b6-member-p
      (p62b6-r-carrier ctx) constant)
     (p62b6-constant-value-p
      ctx n a b constant))))

(defun-sk p62b6-matches-phase-at-p
    (ctx n a b phase x)
  (exists (polynomial-value cosine-value)
    (let ((argument
           (p62b6-r-add-value
            ctx
            (p62b6-r-mul-value
             ctx (p62b6-r-nat ctx n) x)
            phase)))
      (and
       (p62b6-polynomial-value-p
        ctx n a b x polynomial-value)
       (p62b6-cosine-value-p
        ctx argument cosine-value)
       (equal polynomial-value cosine-value)))))

(defun-sk p62b6-phase-identity-p
    (ctx n a b phase)
  (forall (x)
    (implies
     (p62b6-member-p (p62b6-r-carrier ctx) x)
     (p62b6-matches-phase-at-p
      ctx n a b phase x))))

(defun-sk p62b6-phase-exists-p
    (ctx n a b)
  (exists (phase)
    (and
     (p62b6-member-p (p62b6-r-carrier ctx) phase)
     (p62b6-phase-identity-p
      ctx n a b phase))))

(defun putnambench-putnam-1962-b6-statement
    (ctx n a b extreme-points)
  (implies
   (and
    (p62b6-context-p ctx)
    (natp n)
    (true-listp a)
    (true-listp b)
    (equal (len a) (+ n 1))
    (equal (len b) (+ n 1))
    (p62b6-real-list-p ctx a)
    (p62b6-real-list-p ctx b)
    (p62b6-source-hypotheses-p
     ctx n a b extreme-points)
    (not
     (p62b6-constant-exists-p
      ctx n a b)))
   (p62b6-phase-exists-p
    ctx n a b)))

(value-triple :itpeval-statement-checked)
:q
