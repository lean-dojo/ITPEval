;; Statement-only formalization of thousand-theorems corpus artifact Q931001,
;; "Inverse function theorem": a function between normed spaces whose strict
;; derivative at a point is a continuous linear equivalence has a choice-built
;; local inverse with the inverse strict derivative. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Carriers, operations, sets, and functions are unrestricted ACL2 objects.
;; Conservative application interfaces interpret those objects, while native
;; DEFUN-SK forms keep all mathematical quantifiers internal. Norms are
;; represented by rational upper cuts, so no real norm is restricted to
;; rational values. Conservative choices below mirror the source definition's
;; Classical.choose and Function.invFunOn construction.

(defstub q931001-member-p (predicate object) t)

(defstub q931001-unary-value (function object) t)

(defstub q931001-binary-value (function left right) t)

(defun q931001-positive-rational-p (value)
  (and (rationalp value) (< 0 value)))

(defstub q931001-norm-lt-p (norm-lt object bound) t)

(defun-sk q931001-norm-finite-p (norm-lt object)
  (exists (bound)
    (and
     (q931001-positive-rational-p bound)
     (q931001-norm-lt-p norm-lt object bound))))

(defun-sk q931001-norm-positive-p (norm-lt object)
  (exists (bound)
    (and
     (q931001-positive-rational-p bound)
     (not (q931001-norm-lt-p norm-lt object bound)))))

(defun-sk q931001-norm-rounded-p (norm-lt object bound)
  (exists (smaller)
    (and
     (q931001-positive-rational-p smaller)
     (rationalp bound)
     (< smaller bound)
     (q931001-norm-lt-p norm-lt object smaller))))

(defun-sk q931001-norm-product-lt-p
    (left-norm-lt right-norm-lt left right bound)
  (exists (left-bound right-bound)
    (and
     (q931001-positive-rational-p bound)
     (q931001-positive-rational-p left-bound)
     (q931001-positive-rational-p right-bound)
     (q931001-norm-lt-p left-norm-lt left left-bound)
     (q931001-norm-lt-p right-norm-lt right right-bound)
     (< (* left-bound right-bound) bound))))

;; A nontrivially normed field, presented without restricting its carrier.

(defun-sk q931001-field-closure-p
    (carrier add multiply negate inverse)
  (forall (x y)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y))
     (and
      (q931001-member-p
       carrier (q931001-binary-value add x y))
      (q931001-member-p
       carrier (q931001-binary-value multiply x y))
      (q931001-member-p
       carrier (q931001-unary-value negate x))
      (q931001-member-p
       carrier (q931001-unary-value inverse x))))))

(defun-sk q931001-field-additive-laws-p
    (carrier add negate zero)
  (forall (x y z)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y)
      (q931001-member-p carrier z))
     (and
      (equal
       (q931001-binary-value
        add (q931001-binary-value add x y) z)
       (q931001-binary-value
        add x (q931001-binary-value add y z)))
      (equal
       (q931001-binary-value add x y)
       (q931001-binary-value add y x))
      (equal (q931001-binary-value add x zero) x)
      (equal
       (q931001-binary-value
        add x (q931001-unary-value negate x))
       zero)))))

(defun-sk q931001-field-multiplicative-laws-p
    (carrier multiply inverse zero one)
  (forall (x y z)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y)
      (q931001-member-p carrier z))
     (and
      (equal
       (q931001-binary-value
        multiply (q931001-binary-value multiply x y) z)
       (q931001-binary-value
        multiply x (q931001-binary-value multiply y z)))
      (equal
       (q931001-binary-value multiply x y)
       (q931001-binary-value multiply y x))
      (equal (q931001-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (q931001-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (q931001-binary-value
         multiply x (q931001-unary-value inverse x))
        one))))))

(defun-sk q931001-field-distributive-p
    (carrier add multiply)
  (forall (x y z)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y)
      (q931001-member-p carrier z))
      (equal
       (q931001-binary-value
        multiply x (q931001-binary-value add y z))
       (q931001-binary-value
        add
        (q931001-binary-value multiply x y)
        (q931001-binary-value multiply x z))))))

(defun-sk q931001-norm-cut-laws-p (carrier norm-lt zero)
  (forall (x q r)
    (implies
     (q931001-member-p carrier x)
     (and
      (implies
       (q931001-norm-lt-p norm-lt x q)
       (q931001-positive-rational-p q))
      (implies
       (and
        (q931001-norm-lt-p norm-lt x q)
        (rationalp r)
        (< q r))
       (q931001-norm-lt-p norm-lt x r))
      (implies
       (q931001-norm-lt-p norm-lt x q)
       (q931001-norm-rounded-p norm-lt x q))
      (q931001-norm-finite-p norm-lt x)
      (iff
       (equal x zero)
       (not (q931001-norm-positive-p norm-lt x)))))))

(defun-sk q931001-field-norm-zero-one-p (norm-lt zero one)
  (forall (q)
    (and
      (iff
       (q931001-norm-lt-p norm-lt zero q)
       (q931001-positive-rational-p q))
      (iff
       (q931001-norm-lt-p norm-lt one q)
       (and (rationalp q) (< 1 q))))))

(defun-sk q931001-field-norm-negate-p
    (carrier negate norm-lt)
  (forall (x q)
    (implies
     (q931001-member-p carrier x)
      (iff
       (q931001-norm-lt-p
        norm-lt (q931001-unary-value negate x) q)
       (q931001-norm-lt-p norm-lt x q)))))

(defun-sk q931001-field-norm-add-p
    (carrier add norm-lt)
  (forall (x y r s)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y))
      (implies
       (and
        (q931001-positive-rational-p r)
        (q931001-positive-rational-p s)
        (q931001-norm-lt-p norm-lt x r)
        (q931001-norm-lt-p norm-lt y s))
       (q931001-norm-lt-p
        norm-lt (q931001-binary-value add x y) (+ r s))))))

(defun-sk q931001-field-norm-multiply-p
    (carrier multiply norm-lt)
  (forall (x y q)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y))
      (iff
       (q931001-norm-lt-p
        norm-lt (q931001-binary-value multiply x y) q)
       (q931001-norm-product-lt-p
        norm-lt norm-lt x y q)))))

(defun-sk q931001-field-norm-nontrivial-p
    (carrier norm-lt)
  (exists (x bound)
    (and
     (q931001-member-p carrier x)
     (q931001-positive-rational-p bound)
     (< 1 bound)
     (not (q931001-norm-lt-p norm-lt x bound)))))

(defun q931001-nontrivially-normed-field-p
    (carrier add multiply negate inverse zero one norm-lt)
  (and
   (q931001-member-p carrier zero)
   (q931001-member-p carrier one)
   (not (equal zero one))
   (q931001-field-closure-p
    carrier add multiply negate inverse)
   (q931001-field-additive-laws-p carrier add negate zero)
   (q931001-field-multiplicative-laws-p
    carrier multiply inverse zero one)
   (q931001-field-distributive-p carrier add multiply)
   (q931001-norm-cut-laws-p carrier norm-lt zero)
   (q931001-field-norm-zero-one-p norm-lt zero one)
   (q931001-field-norm-negate-p carrier negate norm-lt)
   (q931001-field-norm-add-p carrier add norm-lt)
   (q931001-field-norm-multiply-p
    carrier multiply norm-lt)
   (q931001-field-norm-nontrivial-p carrier norm-lt)))

;; Normed vector spaces over the represented field.

(defun-sk q931001-space-closure-p
    (field-carrier carrier add negate scalar-multiply)
  (forall (a x y)
    (implies
     (and
      (q931001-member-p field-carrier a)
      (q931001-member-p carrier x)
      (q931001-member-p carrier y))
     (and
      (q931001-member-p
       carrier (q931001-binary-value add x y))
      (q931001-member-p
       carrier (q931001-unary-value negate x))
      (q931001-member-p
       carrier (q931001-binary-value scalar-multiply a x))
      ))))

(defun-sk q931001-space-additive-laws-p
    (carrier add negate zero)
  (forall (x y z)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y)
      (q931001-member-p carrier z))
     (and
      (equal
       (q931001-binary-value
        add (q931001-binary-value add x y) z)
       (q931001-binary-value
        add x (q931001-binary-value add y z)))
      (equal
       (q931001-binary-value add x y)
       (q931001-binary-value add y x))
      (equal (q931001-binary-value add x zero) x)
      (equal
       (q931001-binary-value
        add x (q931001-unary-value negate x))
       zero)))))

(defun-sk q931001-space-module-laws-p
    (field-carrier field-add field-multiply field-one
     carrier add scalar-multiply)
  (forall (a b x y)
    (implies
     (and
      (q931001-member-p field-carrier a)
      (q931001-member-p field-carrier b)
      (q931001-member-p carrier x)
      (q931001-member-p carrier y))
     (and
      (equal
       (q931001-binary-value scalar-multiply field-one x)
       x)
      (equal
       (q931001-binary-value
        scalar-multiply
        (q931001-binary-value field-multiply a b)
        x)
       (q931001-binary-value
        scalar-multiply
        a
        (q931001-binary-value scalar-multiply b x)))
      (equal
       (q931001-binary-value
        scalar-multiply
        (q931001-binary-value field-add a b)
        x)
       (q931001-binary-value
        add
        (q931001-binary-value scalar-multiply a x)
        (q931001-binary-value scalar-multiply b x)))
      (equal
       (q931001-binary-value
        scalar-multiply a (q931001-binary-value add x y))
       (q931001-binary-value
        add
        (q931001-binary-value scalar-multiply a x)
        (q931001-binary-value scalar-multiply a y)))
      ))))

(defun-sk q931001-space-norm-negate-p
    (carrier negate norm-lt)
  (forall (x q)
    (implies
     (q931001-member-p carrier x)
     (iff
      (q931001-norm-lt-p
       norm-lt (q931001-unary-value negate x) q)
      (q931001-norm-lt-p norm-lt x q)))))

(defun-sk q931001-space-norm-add-p
    (carrier add norm-lt)
  (forall (x y r s)
    (implies
     (and
      (q931001-member-p carrier x)
      (q931001-member-p carrier y))
     (implies
      (and
       (q931001-positive-rational-p r)
       (q931001-positive-rational-p s)
       (q931001-norm-lt-p norm-lt x r)
       (q931001-norm-lt-p norm-lt y s))
      (q931001-norm-lt-p
       norm-lt (q931001-binary-value add x y) (+ r s))))))

(defun-sk q931001-space-norm-smul-p
    (field-carrier field-norm-lt carrier scalar-multiply norm-lt)
  (forall (a x q)
    (implies
     (and
      (q931001-member-p field-carrier a)
      (q931001-member-p carrier x))
     (iff
      (q931001-norm-lt-p
       norm-lt
       (q931001-binary-value scalar-multiply a x)
       q)
      (q931001-norm-product-lt-p
       field-norm-lt norm-lt a x q)))))

(defun q931001-space-laws-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (and
   (q931001-space-closure-p
    field-carrier carrier add negate scalar-multiply)
   (q931001-space-additive-laws-p carrier add negate zero)
   (q931001-space-module-laws-p
    field-carrier field-add field-multiply field-one
    carrier add scalar-multiply)
   (q931001-norm-cut-laws-p carrier norm-lt zero)
   (q931001-space-norm-negate-p carrier negate norm-lt)
   (q931001-space-norm-add-p carrier add norm-lt)
   (q931001-space-norm-smul-p
    field-carrier field-norm-lt carrier scalar-multiply norm-lt)))

(defun q931001-normed-space-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (and
   (q931001-member-p carrier zero)
   (q931001-space-laws-p
    field-carrier field-add field-multiply field-one field-norm-lt
    carrier add negate zero scalar-multiply norm-lt)))

(defun q931001-vector-difference (add negate left right)
  (q931001-binary-value
   add left (q931001-unary-value negate right)))

;; Sequential completeness is equivalent to metric completeness here.

(defun-sk q931001-sequence-values-p (carrier sequence)
  (forall (index)
    (implies
     (natp index)
     (q931001-member-p
      carrier (q931001-unary-value sequence index)))))

(defun q931001-sequence-p (carrier sequence)
  (q931001-sequence-values-p carrier sequence))

(defun-sk q931001-cauchy-tail-p
    (carrier add negate norm-lt sequence epsilon start)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (natp start)
      (<= start left-index)
      (<= start right-index))
     (q931001-norm-lt-p
      norm-lt
      (q931001-vector-difference
       add negate
       (q931001-unary-value sequence left-index)
       (q931001-unary-value sequence right-index))
      epsilon))))

(defun-sk q931001-cauchy-start-exists-p
    (carrier add negate norm-lt sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q931001-cauchy-tail-p
      carrier add negate norm-lt sequence epsilon start))))

(defun-sk q931001-cauchy-p
    (carrier add negate norm-lt sequence)
  (forall (epsilon)
    (implies
     (q931001-positive-rational-p epsilon)
     (q931001-cauchy-start-exists-p
      carrier add negate norm-lt sequence epsilon))))

(defun-sk q931001-convergence-tail-p
    (carrier add negate norm-lt sequence limit epsilon start)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp start)
      (<= start index))
     (q931001-norm-lt-p
      norm-lt
      (q931001-vector-difference
       add negate
       (q931001-unary-value sequence index)
       limit)
      epsilon))))

(defun-sk q931001-convergence-start-exists-p
    (carrier add negate norm-lt sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q931001-convergence-tail-p
      carrier add negate norm-lt
      sequence limit epsilon start))))

(defun-sk q931001-converges-p
    (carrier add negate norm-lt sequence limit)
  (forall (epsilon)
    (implies
     (q931001-positive-rational-p epsilon)
     (q931001-convergence-start-exists-p
      carrier add negate norm-lt sequence limit epsilon))))

(defun-sk q931001-limit-exists-p
    (carrier add negate norm-lt sequence)
  (exists (limit)
    (and
     (q931001-member-p carrier limit)
     (q931001-converges-p
      carrier add negate norm-lt sequence limit))))

(defun-sk q931001-complete-space-p
    (carrier add negate norm-lt)
  (forall (sequence)
    (implies
     (and
      (q931001-sequence-p carrier sequence)
      (q931001-cauchy-p
       carrier add negate norm-lt sequence))
     (q931001-limit-exists-p
      carrier add negate norm-lt sequence))))

(defun q931001-banach-space-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (and
   (q931001-normed-space-p
    field-carrier field-add field-multiply field-one field-norm-lt
    carrier add negate zero scalar-multiply norm-lt)
   (q931001-complete-space-p carrier add negate norm-lt)))

;; Packed field and normed-space structures.

(defun q931001-field-carrier (field) (nth 0 field))
(defun q931001-field-add (field) (nth 1 field))
(defun q931001-field-multiply (field) (nth 2 field))
(defun q931001-field-negate (field) (nth 3 field))
(defun q931001-field-inverse (field) (nth 4 field))
(defun q931001-field-zero (field) (nth 5 field))
(defun q931001-field-one (field) (nth 6 field))
(defun q931001-field-norm-lt (field) (nth 7 field))

(defun q931001-space-carrier (space) (nth 0 space))
(defun q931001-space-add (space) (nth 1 space))
(defun q931001-space-negate (space) (nth 2 space))
(defun q931001-space-zero (space) (nth 3 space))
(defun q931001-space-smul (space) (nth 4 space))
(defun q931001-space-norm-lt (space) (nth 5 space))

(defun q931001-field-p (field)
  (and
   (true-listp field)
   (equal (len field) 8)
   (q931001-nontrivially-normed-field-p
    (q931001-field-carrier field)
    (q931001-field-add field)
    (q931001-field-multiply field)
    (q931001-field-negate field)
    (q931001-field-inverse field)
    (q931001-field-zero field)
    (q931001-field-one field)
    (q931001-field-norm-lt field))))

(defun q931001-banach-space-context-p (field space)
  (and
   (true-listp space)
   (equal (len space) 6)
   (q931001-banach-space-p
    (q931001-field-carrier field)
    (q931001-field-add field)
    (q931001-field-multiply field)
    (q931001-field-one field)
    (q931001-field-norm-lt field)
    (q931001-space-carrier space)
    (q931001-space-add space)
    (q931001-space-negate space)
    (q931001-space-zero space)
    (q931001-space-smul space)
    (q931001-space-norm-lt space))))

(defun q931001-normed-space-context-p (field space)
  (and
   (true-listp space)
   (equal (len space) 6)
   (q931001-normed-space-p
    (q931001-field-carrier field)
    (q931001-field-add field)
    (q931001-field-multiply field)
    (q931001-field-one field)
    (q931001-field-norm-lt field)
    (q931001-space-carrier space)
    (q931001-space-add space)
    (q931001-space-negate space)
    (q931001-space-zero space)
    (q931001-space-smul space)
    (q931001-space-norm-lt space))))

;; Typed functions and continuous linear maps.

(defun-sk q931001-function-values-p
    (domain-carrier codomain-carrier function)
  (forall (x)
    (implies
     (q931001-member-p domain-carrier x)
     (q931001-member-p
      codomain-carrier (q931001-unary-value function x)))))

(defun q931001-function-p
    (domain-carrier codomain-carrier function)
  (q931001-function-values-p
   domain-carrier codomain-carrier function))

(defun-sk q931001-binary-function-values-p
    (left-carrier right-carrier codomain-carrier function)
  (forall (left right)
    (implies
     (and
      (q931001-member-p left-carrier left)
      (q931001-member-p right-carrier right))
     (q931001-member-p
      codomain-carrier
      (q931001-binary-value function left right)))))

(defun q931001-binary-function-p
    (left-carrier right-carrier codomain-carrier function)
  (q931001-binary-function-values-p
   left-carrier right-carrier codomain-carrier function))

(defun-sk q931001-linear-map-laws-p
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add domain-smul codomain-smul mapping)
  (forall (scalar left right)
    (implies
     (and
      (q931001-member-p field-carrier scalar)
      (q931001-member-p domain-carrier left)
      (q931001-member-p domain-carrier right))
     (and
      (q931001-member-p
       codomain-carrier (q931001-unary-value mapping left))
      (equal
       (q931001-unary-value
        mapping (q931001-binary-value domain-add left right))
       (q931001-binary-value
        codomain-add
        (q931001-unary-value mapping left)
        (q931001-unary-value mapping right)))
      (equal
       (q931001-unary-value
        mapping (q931001-binary-value domain-smul scalar left))
       (q931001-binary-value
        codomain-smul scalar
        (q931001-unary-value mapping left)))))))

(defun q931001-linear-map-p
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add domain-smul codomain-smul mapping)
  (q931001-linear-map-laws-p
   field-carrier domain-carrier codomain-carrier
   domain-add codomain-add domain-smul codomain-smul mapping))

(defun-sk q931001-continuity-at-zero-delta-p
    (domain-space codomain-space mapping epsilon delta)
  (forall (x)
    (implies
     (and
      (q931001-member-p
       (q931001-space-carrier domain-space) x)
      (q931001-norm-lt-p
       (q931001-space-norm-lt domain-space) x delta))
     (q931001-norm-lt-p
      (q931001-space-norm-lt codomain-space)
      (q931001-unary-value mapping x)
      epsilon))))

(defun-sk q931001-continuity-at-zero-delta-exists-p
    (domain-space codomain-space mapping epsilon)
  (exists (delta)
    (and
     (q931001-positive-rational-p delta)
     (q931001-continuity-at-zero-delta-p
      domain-space codomain-space mapping epsilon delta))))

(defun-sk q931001-continuous-at-zero-p
    (domain-space codomain-space mapping)
  (forall (epsilon)
    (implies
     (q931001-positive-rational-p epsilon)
     (q931001-continuity-at-zero-delta-exists-p
      domain-space codomain-space mapping epsilon))))

(defun q931001-continuous-linear-map-p
    (field domain-space codomain-space mapping)
  (and
   (q931001-linear-map-p
    (q931001-field-carrier field)
    (q931001-space-carrier domain-space)
    (q931001-space-carrier codomain-space)
    (q931001-space-add domain-space)
    (q931001-space-add codomain-space)
    (q931001-space-smul domain-space)
    (q931001-space-smul codomain-space)
    mapping)
   (q931001-continuous-at-zero-p
    domain-space codomain-space mapping)))

;; Exact upper-cut form of A <= epsilon * B.

(defun-sk q931001-scaled-norm-bound-p
    (codomain-norm-lt remainder domain-norm-lt increment epsilon)
  (forall (domain-bound codomain-bound)
    (implies
     (and
      (q931001-positive-rational-p domain-bound)
      (q931001-positive-rational-p codomain-bound)
      (q931001-norm-lt-p
       domain-norm-lt increment domain-bound)
      (< (* epsilon domain-bound) codomain-bound))
     (q931001-norm-lt-p
      codomain-norm-lt remainder codomain-bound))))

(defun-sk q931001-strict-derivative-points-p
    (domain-space codomain-space function derivative
     point epsilon radius)
  (forall (x y)
    (implies
     (and
      (q931001-member-p
       (q931001-space-carrier domain-space) x)
      (q931001-member-p
       (q931001-space-carrier domain-space) y)
      (q931001-norm-lt-p
       (q931001-space-norm-lt domain-space)
       (q931001-vector-difference
        (q931001-space-add domain-space)
        (q931001-space-negate domain-space)
        x point)
       radius)
      (q931001-norm-lt-p
       (q931001-space-norm-lt domain-space)
       (q931001-vector-difference
        (q931001-space-add domain-space)
        (q931001-space-negate domain-space)
        y point)
       radius))
     (q931001-scaled-norm-bound-p
      (q931001-space-norm-lt codomain-space)
      (q931001-vector-difference
       (q931001-space-add codomain-space)
       (q931001-space-negate codomain-space)
       (q931001-vector-difference
        (q931001-space-add codomain-space)
        (q931001-space-negate codomain-space)
        (q931001-unary-value function x)
        (q931001-unary-value function y))
       (q931001-unary-value
        derivative
        (q931001-vector-difference
         (q931001-space-add domain-space)
         (q931001-space-negate domain-space)
         x y)))
      (q931001-space-norm-lt domain-space)
      (q931001-vector-difference
       (q931001-space-add domain-space)
       (q931001-space-negate domain-space)
       x y)
      epsilon))))

(defun-sk q931001-strict-derivative-radius-exists-p
    (domain-space codomain-space function derivative point epsilon)
  (exists (radius)
    (and
     (q931001-positive-rational-p radius)
     (q931001-strict-derivative-points-p
      domain-space codomain-space function derivative
      point epsilon radius))))

(defun-sk q931001-has-strict-fderiv-at-p
    (domain-space codomain-space function derivative point)
  (forall (epsilon)
    (implies
     (q931001-positive-rational-p epsilon)
     (q931001-strict-derivative-radius-exists-p
      domain-space codomain-space function derivative
      point epsilon))))

(defun q931001-strict-derivative-data-p
    (domain-space codomain-space function derivative point)
  (and
   (q931001-function-p
    (q931001-space-carrier domain-space)
    (q931001-space-carrier codomain-space)
    function)
   (q931001-has-strict-fderiv-at-p
    domain-space codomain-space function derivative point)))

;; A continuous linear equivalence and its inverse continuous linear map.

(defun q931001-equiv-forward (equiv)
  (nth 0 equiv))

(defun q931001-equiv-inverse (equiv)
  (nth 1 equiv))

(defun-sk q931001-equiv-inverse-laws-p
    (domain-space codomain-space equiv)
  (forall (x y)
    (and
     (implies
      (q931001-member-p
       (q931001-space-carrier domain-space) x)
      (equal
       (q931001-unary-value
        (q931001-equiv-inverse equiv)
        (q931001-unary-value
         (q931001-equiv-forward equiv) x))
       x))
     (implies
      (q931001-member-p
       (q931001-space-carrier codomain-space) y)
      (equal
       (q931001-unary-value
        (q931001-equiv-forward equiv)
        (q931001-unary-value
         (q931001-equiv-inverse equiv) y))
       y)))))

(defun q931001-continuous-linear-equiv-p
    (field domain-space codomain-space equiv)
  (and
   (true-listp equiv)
   (equal (len equiv) 2)
   (q931001-continuous-linear-map-p
    field domain-space codomain-space
    (q931001-equiv-forward equiv))
   (q931001-continuous-linear-map-p
    field codomain-space domain-space
    (q931001-equiv-inverse equiv))
   (q931001-equiv-inverse-laws-p
    domain-space codomain-space equiv)))

;; Open subsets of a normed space.

(defun-sk q931001-set-members-carrier-p (carrier set)
  (forall (x)
    (implies
     (q931001-member-p set x)
     (q931001-member-p carrier x))))

(defun q931001-valid-set-p (carrier set)
  (q931001-set-members-carrier-p carrier set))

(defun-sk q931001-ball-subset-p
    (space set center radius)
  (forall (x)
    (implies
     (and
      (q931001-member-p (q931001-space-carrier space) x)
      (q931001-norm-lt-p
       (q931001-space-norm-lt space)
       (q931001-vector-difference
        (q931001-space-add space)
        (q931001-space-negate space)
        x center)
       radius))
     (q931001-member-p set x))))

(defun-sk q931001-open-radius-exists-p (space set center)
  (exists (radius)
    (and
     (q931001-positive-rational-p radius)
     (q931001-ball-subset-p space set center radius))))

(defun-sk q931001-open-at-every-point-p (space set)
  (forall (center)
    (implies
     (q931001-member-p set center)
     (q931001-open-radius-exists-p space set center))))

(defun q931001-open-set-p (space set)
  (and
   (q931001-valid-set-p
    (q931001-space-carrier space) set)
   (q931001-open-at-every-point-p space set)))

;; Rational upper-cut presentation of the operator norm of the inverse map.

(defun-sk q931001-inverse-linear-bound-p
    (domain-space codomain-space equiv coefficient)
  (forall (input input-bound output-bound)
    (implies
     (and
      (q931001-member-p
       (q931001-space-carrier codomain-space) input)
      (q931001-positive-rational-p coefficient)
      (q931001-positive-rational-p input-bound)
      (q931001-positive-rational-p output-bound)
      (q931001-norm-lt-p
       (q931001-space-norm-lt codomain-space)
       input input-bound)
      (< (* coefficient input-bound) output-bound))
     (q931001-norm-lt-p
      (q931001-space-norm-lt domain-space)
      (q931001-unary-value
       (q931001-equiv-inverse equiv) input)
      output-bound))))

(defun-sk q931001-inverse-operator-norm-lt-p
    (domain-space codomain-space equiv bound)
  (exists (coefficient)
    (and
     (q931001-positive-rational-p bound)
     (q931001-positive-rational-p coefficient)
     (< coefficient bound)
     (q931001-inverse-linear-bound-p
      domain-space codomain-space equiv coefficient))))

(defun-sk q931001-inverse-operator-norm-positive-p
    (domain-space codomain-space equiv)
  (exists (bound)
    (and
     (q931001-positive-rational-p bound)
     (not
      (q931001-inverse-operator-norm-lt-p
       domain-space codomain-space equiv bound)))))

(defun-sk q931001-inverse-operator-norm-greater-p
    (domain-space codomain-space equiv threshold)
  (exists (bound)
    (and
     (q931001-positive-rational-p threshold)
     (q931001-positive-rational-p bound)
     (< threshold bound)
     (not
      (q931001-inverse-operator-norm-lt-p
       domain-space codomain-space equiv bound)))))

;; This is the strict upper-cut relation
;; ||equiv.symm||_+^{-1} / 2 < epsilon.

(defun q931001-half-inverse-operator-norm-lt-p
    (domain-space codomain-space equiv epsilon)
  (and
   (q931001-positive-rational-p epsilon)
   (or
    (not
     (q931001-inverse-operator-norm-positive-p
      domain-space codomain-space equiv))
    (q931001-inverse-operator-norm-greater-p
     domain-space codomain-space equiv
     (/ 1 (* 2 epsilon))))))

(defun q931001-derivative-remainder
    (domain-space codomain-space function derivative x y)
  (q931001-vector-difference
   (q931001-space-add codomain-space)
   (q931001-space-negate codomain-space)
   (q931001-vector-difference
    (q931001-space-add codomain-space)
    (q931001-space-negate codomain-space)
    (q931001-unary-value function x)
    (q931001-unary-value function y))
   (q931001-unary-value
    derivative
    (q931001-vector-difference
     (q931001-space-add domain-space)
     (q931001-space-negate domain-space)
     x y))))

;; ApproximatesLinearOn f equiv.forward source
;; (||equiv.inverse||_+^{-1} / 2), represented by upper cuts.

(defun-sk q931001-approximates-derivative-on-p
    (domain-space codomain-space function equiv source)
  (forall (x y epsilon)
    (implies
     (and
      (q931001-member-p source x)
      (q931001-member-p source y)
      (q931001-half-inverse-operator-norm-lt-p
       domain-space codomain-space equiv epsilon))
     (q931001-scaled-norm-bound-p
      (q931001-space-norm-lt codomain-space)
      (q931001-derivative-remainder
       domain-space codomain-space function
       (q931001-equiv-forward equiv) x y)
      (q931001-space-norm-lt domain-space)
      (q931001-vector-difference
       (q931001-space-add domain-space)
       (q931001-space-negate domain-space)
       x y)
      epsilon))))

;; The source neighbourhood used by
;; HasStrictFDerivAt.toOpenPartialHomeomorph is represented by a concrete open
;; ball.  Choosing its positive rational radius avoids quantifying over an
;; externally supplied family of set tags.

(defun q931001-in-open-ball-p
    (space center radius point)
  (and
   (q931001-member-p
    (q931001-space-carrier space) point)
   (q931001-positive-rational-p radius)
   (q931001-norm-lt-p
    (q931001-space-norm-lt space)
    (q931001-vector-difference
     (q931001-space-add space)
     (q931001-space-negate space)
     point center)
    radius)))

(defun-sk q931001-approximates-derivative-on-ball-p
    (domain-space codomain-space function equiv point radius)
  (forall (x y epsilon)
    (implies
     (and
      (q931001-in-open-ball-p
       domain-space point radius x)
      (q931001-in-open-ball-p
       domain-space point radius y)
      (q931001-half-inverse-operator-norm-lt-p
       domain-space codomain-space equiv epsilon))
     (q931001-scaled-norm-bound-p
      (q931001-space-norm-lt codomain-space)
      (q931001-derivative-remainder
       domain-space codomain-space function
       (q931001-equiv-forward equiv) x y)
      (q931001-space-norm-lt domain-space)
      (q931001-vector-difference
       (q931001-space-add domain-space)
       (q931001-space-negate domain-space)
       x y)
      epsilon))))

(defun q931001-derived-radius-candidate-p
    (domain-space codomain-space function equiv point radius)
  (and
   (q931001-positive-rational-p radius)
   (q931001-approximates-derivative-on-ball-p
    domain-space codomain-space function equiv point radius)))

(defchoose q931001-derived-radius
    (radius)
    (domain-space codomain-space function equiv point)
  (q931001-derived-radius-candidate-p
   domain-space codomain-space function equiv point radius))

;; Function.invFunOn chooses a source preimage when one exists and otherwise
;; chooses an arbitrary element of the nonempty domain carrier.

(defun-sk q931001-source-preimage-exists-p
    (domain-space function point radius image)
  (exists (preimage)
    (and
     (q931001-in-open-ball-p
      domain-space point radius preimage)
     (equal
      (q931001-unary-value function preimage)
      image))))

(defchoose q931001-source-preimage
    (preimage)
    (domain-space function point radius image)
  (and
   (q931001-in-open-ball-p
    domain-space point radius preimage)
   (equal
    (q931001-unary-value function preimage)
    image)))

(defchoose q931001-carrier-default
    (element)
    (carrier)
  (q931001-member-p carrier element))

(defun q931001-local-inverse-value
    (domain-space codomain-space function equiv point image)
  (let ((radius
         (q931001-derived-radius
          domain-space codomain-space function equiv point)))
    (if
     (q931001-source-preimage-exists-p
      domain-space function point radius image)
     (q931001-source-preimage
      domain-space function point radius image)
     (q931001-carrier-default
      (q931001-space-carrier domain-space)))))

(defun-sk q931001-local-inverse-values-p
    (domain-space codomain-space function equiv point)
  (forall (image)
    (implies
     (q931001-member-p
      (q931001-space-carrier codomain-space) image)
     (q931001-member-p
      (q931001-space-carrier domain-space)
      (q931001-local-inverse-value
       domain-space codomain-space function equiv point image)))))

;; Strict derivative of the internally defined local inverse.

(defun q931001-local-inverse-remainder
    (domain-space codomain-space function equiv point x y)
  (q931001-vector-difference
   (q931001-space-add domain-space)
   (q931001-space-negate domain-space)
   (q931001-vector-difference
    (q931001-space-add domain-space)
    (q931001-space-negate domain-space)
    (q931001-local-inverse-value
     domain-space codomain-space function equiv point x)
    (q931001-local-inverse-value
     domain-space codomain-space function equiv point y))
   (q931001-unary-value
    (q931001-equiv-inverse equiv)
    (q931001-vector-difference
     (q931001-space-add codomain-space)
     (q931001-space-negate codomain-space)
     x y))))

(defun-sk q931001-local-inverse-strict-derivative-points-p
    (domain-space codomain-space function equiv point
     image-point epsilon radius)
  (forall (x y)
    (implies
     (and
      (q931001-member-p
       (q931001-space-carrier codomain-space) x)
      (q931001-member-p
       (q931001-space-carrier codomain-space) y)
      (q931001-norm-lt-p
       (q931001-space-norm-lt codomain-space)
       (q931001-vector-difference
        (q931001-space-add codomain-space)
        (q931001-space-negate codomain-space)
        x image-point)
       radius)
      (q931001-norm-lt-p
       (q931001-space-norm-lt codomain-space)
       (q931001-vector-difference
        (q931001-space-add codomain-space)
        (q931001-space-negate codomain-space)
        y image-point)
       radius))
     (q931001-scaled-norm-bound-p
      (q931001-space-norm-lt domain-space)
      (q931001-local-inverse-remainder
       domain-space codomain-space function equiv point x y)
      (q931001-space-norm-lt codomain-space)
      (q931001-vector-difference
       (q931001-space-add codomain-space)
       (q931001-space-negate codomain-space)
       x y)
      epsilon))))

(defun-sk q931001-local-inverse-radius-exists-p
    (domain-space codomain-space function equiv point
     image-point epsilon)
  (exists (radius)
    (and
     (q931001-positive-rational-p radius)
     (q931001-local-inverse-strict-derivative-points-p
      domain-space codomain-space function equiv point
      image-point epsilon radius))))

(defun-sk q931001-local-inverse-has-strict-fderiv-at-p
    (domain-space codomain-space function equiv point image-point)
  (forall (epsilon)
    (implies
     (q931001-positive-rational-p epsilon)
     (q931001-local-inverse-radius-exists-p
      domain-space codomain-space function equiv point
      image-point epsilon))))

(defun q931001-local-inverse-strict-derivative-data-p
    (domain-space codomain-space function equiv point image-point)
  (and
   (q931001-local-inverse-values-p
    domain-space codomain-space function equiv point)
   (q931001-local-inverse-has-strict-fderiv-at-p
    domain-space codomain-space function equiv point image-point)))

(defun-sk
    thousand-theorems-q931001-inverse-function-theorem-statement ()
  (forall (field domain-space codomain-space function equiv point)
    (implies
     (and
      (q931001-field-p field)
      (q931001-banach-space-context-p field domain-space)
      (q931001-normed-space-context-p field codomain-space)
      (q931001-member-p
       (q931001-space-carrier domain-space) point)
      (q931001-continuous-linear-equiv-p
       field domain-space codomain-space equiv)
      (q931001-strict-derivative-data-p
       domain-space codomain-space function
       (q931001-equiv-forward equiv) point))
     (q931001-local-inverse-strict-derivative-data-p
      domain-space codomain-space function equiv point
      (q931001-unary-value function point)))))

(value-triple :itpeval-statement-checked)
:q
