;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_b2:
;; the punctured limit at zero of integral power means on a positive affine
;; interval, with its exact exponential-power value. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers. APPLY$ objects
;; present its carrier and operations without restricting the domain to ACL2
;; rationals. Positive-base real powers are fixed by their rational values and
;; continuity in the exponent. The distinguished value e is fixed by its
;; exponential series. The integral below uses the unbounded tagged-partition
;; criterion; for the continuous source integrand this is equal to its
;; Lebesgue integral. Thus the final predicate states the source punctured
;; real limit itself, not a discretization or a derived integral identity.

(defun p79b2-carrier (ctx) (nth 0 ctx))
(defun p79b2-zero (ctx) (nth 1 ctx))
(defun p79b2-one (ctx) (nth 2 ctx))
(defun p79b2-add-op (ctx) (nth 3 ctx))
(defun p79b2-multiply-op (ctx) (nth 4 ctx))
(defun p79b2-negate-op (ctx) (nth 5 ctx))
(defun p79b2-inverse-op (ctx) (nth 6 ctx))
(defun p79b2-less-op (ctx) (nth 7 ctx))
(defun p79b2-power-op (ctx) (nth 8 ctx))
(defun p79b2-e (ctx) (nth 9 ctx))

(defun p79b2-member-p (ctx x)
  (if (apply$ (p79b2-carrier ctx) (list x)) t nil))

(defun p79b2-unary (operation x)
  (apply$ operation (list x)))

(defun p79b2-binary (operation x y)
  (apply$ operation (list x y)))

(defun p79b2-add (ctx x y)
  (p79b2-binary (p79b2-add-op ctx) x y))

(defun p79b2-multiply (ctx x y)
  (p79b2-binary (p79b2-multiply-op ctx) x y))

(defun p79b2-negate (ctx x)
  (p79b2-unary (p79b2-negate-op ctx) x))

(defun p79b2-inverse (ctx x)
  (p79b2-unary (p79b2-inverse-op ctx) x))

(defun p79b2-less-p (ctx x y)
  (if (p79b2-binary (p79b2-less-op ctx) x y) t nil))

(defun p79b2-power (ctx base exponent)
  (p79b2-binary (p79b2-power-op ctx) base exponent))

(defun p79b2-subtract (ctx x y)
  (p79b2-add ctx x (p79b2-negate ctx y)))

(defun p79b2-divide (ctx x y)
  (p79b2-multiply ctx x (p79b2-inverse ctx y)))

(defun p79b2-less-equal-p (ctx x y)
  (not (p79b2-less-p ctx y x)))

(defun p79b2-positive-p (ctx x)
  (and
   (p79b2-member-p ctx x)
   (p79b2-less-p ctx (p79b2-zero ctx) x)))

(defun p79b2-absolute (ctx x)
  (if (p79b2-less-p ctx x (p79b2-zero ctx))
      (p79b2-negate ctx x)
    x))

(defun p79b2-distance (ctx x y)
  (p79b2-absolute ctx (p79b2-subtract ctx x y)))

(defun-sk p79b2-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p79b2-member-p ctx x)
      (p79b2-member-p ctx y)
      (p79b2-member-p ctx z))
     (and
      (p79b2-member-p ctx (p79b2-add ctx x y))
      (p79b2-member-p ctx (p79b2-multiply ctx x y))
      (p79b2-member-p ctx (p79b2-negate ctx x))
      (p79b2-member-p ctx (p79b2-inverse ctx x))
      (equal
       (p79b2-add ctx (p79b2-add ctx x y) z)
       (p79b2-add ctx x (p79b2-add ctx y z)))
      (equal (p79b2-add ctx x y) (p79b2-add ctx y x))
      (equal (p79b2-add ctx x (p79b2-zero ctx)) x)
      (equal
       (p79b2-add ctx x (p79b2-negate ctx x))
       (p79b2-zero ctx))
      (equal
       (p79b2-multiply ctx (p79b2-multiply ctx x y) z)
       (p79b2-multiply ctx x (p79b2-multiply ctx y z)))
      (equal
       (p79b2-multiply ctx x y)
       (p79b2-multiply ctx y x))
      (equal (p79b2-multiply ctx x (p79b2-one ctx)) x)
      (equal
       (p79b2-inverse ctx (p79b2-zero ctx))
       (p79b2-zero ctx))
      (implies
       (not (equal x (p79b2-zero ctx)))
       (equal
        (p79b2-multiply ctx x (p79b2-inverse ctx x))
        (p79b2-one ctx)))
      (equal
       (p79b2-multiply ctx x (p79b2-add ctx y z))
       (p79b2-add
        ctx
        (p79b2-multiply ctx x y)
        (p79b2-multiply ctx x z)))))))

(defun-sk p79b2-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p79b2-member-p ctx x)
      (p79b2-member-p ctx y)
      (p79b2-member-p ctx z))
     (and
      (not (p79b2-less-p ctx x x))
      (or
       (equal x y)
       (p79b2-less-p ctx x y)
       (p79b2-less-p ctx y x))
      (implies
       (and
        (p79b2-less-p ctx x y)
        (p79b2-less-p ctx y z))
       (p79b2-less-p ctx x z))
      (implies
       (p79b2-less-p ctx x y)
       (p79b2-less-p
        ctx
        (p79b2-add ctx x z)
        (p79b2-add ctx y z)))
      (implies
       (and
        (p79b2-less-p ctx (p79b2-zero ctx) x)
        (p79b2-less-p ctx (p79b2-zero ctx) y))
       (p79b2-less-p
        ctx
        (p79b2-zero ctx)
        (p79b2-multiply ctx x y)))))))

(defun-sk p79b2-valid-set-p (ctx set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p79b2-member-p ctx x))))

(defun-sk p79b2-set-nonempty-p (ctx set)
  (exists (x)
    (and
     (p79b2-member-p ctx x)
     (apply$ set (list x)))))

(defun-sk p79b2-upper-bound-p (ctx set bound)
  (forall (x)
    (implies
     (and
      (p79b2-member-p ctx x)
      (apply$ set (list x)))
     (not (p79b2-less-p ctx bound x)))))

(defun-sk p79b2-bounded-above-p (ctx set)
  (exists (bound)
    (and
     (p79b2-member-p ctx bound)
     (p79b2-upper-bound-p ctx set bound))))

(defun-sk p79b2-supremum-p (ctx set supremum)
  (forall (bound)
    (and
     (p79b2-member-p ctx supremum)
     (p79b2-upper-bound-p ctx set supremum)
     (implies
      (and
       (p79b2-member-p ctx bound)
       (p79b2-upper-bound-p ctx set bound))
      (not (p79b2-less-p ctx bound supremum))))))

(defun-sk p79b2-has-supremum-p (ctx set)
  (exists (supremum)
    (p79b2-supremum-p ctx set supremum)))

(defun-sk p79b2-dedekind-complete-p (ctx)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p79b2-valid-set-p ctx set)
      (p79b2-set-nonempty-p ctx set)
      (p79b2-bounded-above-p ctx set))
     (p79b2-has-supremum-p ctx set))))

(defun p79b2-natural (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p79b2-zero ctx)
    (p79b2-add
     ctx
     (p79b2-one ctx)
     (p79b2-natural ctx (- n 1)))))

(defun p79b2-integer (ctx n)
  (if (< n 0)
      (p79b2-negate ctx (p79b2-natural ctx (- n)))
    (p79b2-natural ctx n)))

(defun p79b2-natural-power (ctx base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p79b2-one ctx)
    (p79b2-multiply
     ctx
     (p79b2-natural-power ctx base (- exponent 1))
     base)))

(defun p79b2-integer-power (ctx base exponent)
  (if (< exponent 0)
      (p79b2-inverse
       ctx
       (p79b2-natural-power ctx base (- exponent)))
    (p79b2-natural-power ctx base exponent)))

(defun-sk p79b2-power-typing-p (ctx)
  (forall (base exponent)
    (implies
     (and
      (p79b2-positive-p ctx base)
      (p79b2-member-p ctx exponent))
     (p79b2-positive-p
      ctx
      (p79b2-power ctx base exponent)))))

(defun-sk p79b2-power-rational-laws-p (ctx)
  (forall (base numerator denominator)
    (implies
     (and
      (p79b2-positive-p ctx base)
      (integerp numerator)
      (posp denominator))
     (equal
      (p79b2-natural-power
       ctx
       (p79b2-power
        ctx
        base
        (p79b2-multiply
         ctx
         (p79b2-integer ctx numerator)
         (p79b2-inverse
          ctx
          (p79b2-natural ctx denominator))))
       denominator)
      (p79b2-integer-power ctx base numerator)))))

(defun-sk p79b2-power-neighborhood-p
    (ctx base exponent epsilon delta)
  (forall (y)
    (implies
     (and
      (p79b2-member-p ctx y)
      (p79b2-less-p
       ctx
       (p79b2-distance ctx y exponent)
       delta))
     (p79b2-less-p
      ctx
      (p79b2-distance
       ctx
       (p79b2-power ctx base y)
       (p79b2-power ctx base exponent))
      epsilon))))

(defun-sk p79b2-power-delta-exists-p
    (ctx base exponent epsilon)
  (exists (delta)
    (and
     (p79b2-positive-p ctx delta)
     (p79b2-power-neighborhood-p
      ctx base exponent epsilon delta))))

(defun-sk p79b2-power-continuous-p (ctx)
  (forall (base exponent epsilon)
    (implies
     (and
      (p79b2-positive-p ctx base)
      (p79b2-member-p ctx exponent)
      (p79b2-positive-p ctx epsilon))
     (p79b2-power-delta-exists-p
      ctx base exponent epsilon))))

(defun p79b2-real-power-p (ctx)
  (and
   (tamep-functionp (p79b2-power-op ctx))
   (p79b2-power-typing-p ctx)
   (p79b2-power-rational-laws-p ctx)
   (p79b2-power-continuous-p ctx)))

(defun p79b2-factorial-value (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p79b2-one ctx)
    (p79b2-multiply
     ctx
     (p79b2-natural ctx n)
     (p79b2-factorial-value ctx (- n 1)))))

(defun p79b2-e-prefix (ctx terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p79b2-zero ctx)
    (let ((index (- terms 1)))
      (p79b2-add
       ctx
       (p79b2-e-prefix ctx index)
       (p79b2-inverse
        ctx
        (p79b2-factorial-value ctx index))))))

(defun-sk p79b2-e-tail-p (ctx epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p79b2-less-p
      ctx
      (p79b2-distance
       ctx
       (p79b2-e-prefix ctx terms)
       (p79b2-e ctx))
      epsilon))))

(defun-sk p79b2-e-cutoff-exists-p (ctx epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p79b2-e-tail-p ctx epsilon cutoff))))

(defun-sk p79b2-e-converges-p (ctx)
  (forall (epsilon)
    (implies
     (p79b2-positive-p ctx epsilon)
     (p79b2-e-cutoff-exists-p ctx epsilon))))

(defun p79b2-e-value-p (ctx)
  (and
   (p79b2-positive-p ctx (p79b2-e ctx))
   (p79b2-e-converges-p ctx)))

(defun p79b2-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 10)
   (tamep-functionp (p79b2-carrier ctx))
   (tamep-functionp (p79b2-add-op ctx))
   (tamep-functionp (p79b2-multiply-op ctx))
   (tamep-functionp (p79b2-negate-op ctx))
   (tamep-functionp (p79b2-inverse-op ctx))
   (tamep-functionp (p79b2-less-op ctx))
   (p79b2-member-p ctx (p79b2-zero ctx))
   (p79b2-member-p ctx (p79b2-one ctx))
   (not (equal (p79b2-zero ctx) (p79b2-one ctx)))
   (p79b2-field-laws-p ctx)
   (p79b2-order-laws-p ctx)
   (p79b2-less-p ctx (p79b2-zero ctx) (p79b2-one ctx))
   (p79b2-dedekind-complete-p ctx)
   (p79b2-real-power-p ctx)
   (p79b2-e-value-p ctx)))

(defun p79b2-real-list-p (ctx values)
  (if (consp values)
      (and
       (p79b2-member-p ctx (car values))
       (p79b2-real-list-p ctx (cdr values)))
    (equal values nil)))

(defun p79b2-strictly-increasing-p (ctx values)
  (if (and (consp values) (consp (cdr values)))
      (and
       (p79b2-less-p ctx (car values) (cadr values))
       (p79b2-strictly-increasing-p ctx (cdr values)))
    (and (consp values) (endp (cdr values)))))

(defun p79b2-tags-fit-p (ctx nodes tags)
  (if (consp tags)
      (and
       (consp nodes)
       (consp (cdr nodes))
       (p79b2-less-equal-p ctx (car nodes) (car tags))
       (p79b2-less-equal-p ctx (car tags) (cadr nodes))
       (p79b2-tags-fit-p ctx (cdr nodes) (cdr tags)))
    (and
     (consp nodes)
     (endp (cdr nodes))
     (equal tags nil))))

(defun p79b2-tagged-unit-partition-p (ctx nodes tags)
  (and
   (true-listp nodes)
   (true-listp tags)
   (p79b2-real-list-p ctx nodes)
   (p79b2-real-list-p ctx tags)
   (p79b2-strictly-increasing-p ctx nodes)
   (p79b2-tags-fit-p ctx nodes tags)
   (equal (car nodes) (p79b2-zero ctx))
   (equal (car (last nodes)) (p79b2-one ctx))))

(defun p79b2-mesh-less-p (ctx nodes delta)
  (if (and (consp nodes) (consp (cdr nodes)))
      (and
       (p79b2-less-p
        ctx
        (p79b2-subtract ctx (cadr nodes) (car nodes))
        delta)
       (p79b2-mesh-less-p ctx (cdr nodes) delta))
    (and (consp nodes) (endp (cdr nodes)))))

(defun p79b2-affine-value (ctx a b x)
  (p79b2-add
   ctx
   (p79b2-multiply ctx b x)
   (p79b2-multiply
    ctx
    a
    (p79b2-subtract ctx (p79b2-one ctx) x))))

(defun p79b2-integrand-value (ctx a b tau x)
  (p79b2-power
   ctx
   (p79b2-affine-value ctx a b x)
   tau))

(defun p79b2-riemann-sum (ctx a b tau nodes tags)
  (if (consp tags)
      (p79b2-add
       ctx
       (p79b2-multiply
        ctx
        (p79b2-integrand-value ctx a b tau (car tags))
        (p79b2-subtract ctx (cadr nodes) (car nodes)))
       (p79b2-riemann-sum
        ctx a b tau (cdr nodes) (cdr tags)))
    (p79b2-zero ctx)))

(defun-sk p79b2-integral-delta-p
    (ctx a b tau value epsilon delta)
  (forall (nodes tags)
    (implies
     (and
      (p79b2-tagged-unit-partition-p ctx nodes tags)
      (p79b2-mesh-less-p ctx nodes delta))
     (p79b2-less-p
      ctx
      (p79b2-distance
       ctx
       (p79b2-riemann-sum ctx a b tau nodes tags)
       value)
      epsilon))))

(defun-sk p79b2-integral-delta-exists-p
    (ctx a b tau value epsilon)
  (exists (delta)
    (and
     (p79b2-positive-p ctx delta)
     (p79b2-integral-delta-p
      ctx a b tau value epsilon delta))))

(defun-sk p79b2-integral-converges-p
    (ctx a b tau value)
  (forall (epsilon)
    (implies
     (p79b2-positive-p ctx epsilon)
     (p79b2-integral-delta-exists-p
      ctx a b tau value epsilon))))

(defun p79b2-integral-value-p (ctx a b tau value)
  (and
   (p79b2-member-p ctx a)
   (p79b2-member-p ctx b)
   (p79b2-member-p ctx tau)
   (p79b2-positive-p ctx value)
   (p79b2-integral-converges-p ctx a b tau value)))

(defun p79b2-solution-value (ctx a b)
  (let* ((b-minus-a (p79b2-subtract ctx b a))
         (b-to-b (p79b2-power ctx b b))
         (a-to-a (p79b2-power ctx a a))
         (power-ratio (p79b2-divide ctx b-to-b a-to-a)))
    (p79b2-multiply
     ctx
     (p79b2-inverse ctx (p79b2-e ctx))
     (p79b2-power
      ctx
      power-ratio
      (p79b2-inverse ctx b-minus-a)))))

(defun-sk p79b2-mean-close-exists-p
    (ctx a b tau solution epsilon)
  (exists (integral)
    (and
     (p79b2-integral-value-p ctx a b tau integral)
     (p79b2-less-p
      ctx
      (p79b2-distance
       ctx
       (p79b2-power ctx integral (p79b2-inverse ctx tau))
       solution)
      epsilon))))

(defun-sk p79b2-limit-neighborhood-p
    (ctx a b solution epsilon delta)
  (forall (tau)
    (implies
     (and
      (p79b2-member-p ctx tau)
      (p79b2-positive-p ctx (p79b2-absolute ctx tau))
      (p79b2-less-p ctx (p79b2-absolute ctx tau) delta))
     (p79b2-mean-close-exists-p
      ctx a b tau solution epsilon))))

(defun-sk p79b2-limit-delta-exists-p
    (ctx a b solution epsilon)
  (exists (delta)
    (and
     (p79b2-positive-p ctx delta)
     (p79b2-limit-neighborhood-p
      ctx a b solution epsilon delta))))

(defun-sk p79b2-source-limit-p (ctx a b solution)
  (forall (epsilon)
    (implies
     (p79b2-positive-p ctx epsilon)
     (p79b2-limit-delta-exists-p
      ctx a b solution epsilon))))

(defun-sk putnambench-putnam-1979-b2-statement (ctx)
  (forall (a b)
    (implies
     (and
      (p79b2-context-p ctx)
      (p79b2-positive-p ctx a)
      (p79b2-member-p ctx b)
      (p79b2-less-p ctx a b))
     (p79b2-source-limit-p
      ctx a b (p79b2-solution-value ctx a b)))))

(value-triple :itpeval-statement-checked)
:q
