;; Statement-only formalization of thousand-theorems corpus artifact Q848375,
;; "Implicit function theorem": for arbitrary Banach-space implicit-function
;; data, the implicit function is the curried inverse of the derived local open
;; partial homeomorphism. This file contains no proof.

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

(defstub q848375-member-p (predicate object) t)

(defstub q848375-unary-value (function object) t)

(defstub q848375-binary-value (function left right) t)

(defun q848375-positive-rational-p (value)
  (and (rationalp value) (< 0 value)))

(defstub q848375-norm-lt-p (norm-lt object bound) t)

(defun-sk q848375-norm-finite-p (norm-lt object)
  (exists (bound)
    (and
     (q848375-positive-rational-p bound)
     (q848375-norm-lt-p norm-lt object bound))))

(defun-sk q848375-norm-positive-p (norm-lt object)
  (exists (bound)
    (and
     (q848375-positive-rational-p bound)
     (not (q848375-norm-lt-p norm-lt object bound)))))

(defun-sk q848375-norm-rounded-p (norm-lt object bound)
  (exists (smaller)
    (and
     (q848375-positive-rational-p smaller)
     (rationalp bound)
     (< smaller bound)
     (q848375-norm-lt-p norm-lt object smaller))))

(defun-sk q848375-norm-product-lt-p
    (left-norm-lt right-norm-lt left right bound)
  (exists (left-bound right-bound)
    (and
     (q848375-positive-rational-p bound)
     (q848375-positive-rational-p left-bound)
     (q848375-positive-rational-p right-bound)
     (q848375-norm-lt-p left-norm-lt left left-bound)
     (q848375-norm-lt-p right-norm-lt right right-bound)
     (< (* left-bound right-bound) bound))))

;; A nontrivially normed field, presented without restricting its carrier.

(defun-sk q848375-field-closure-p
    (carrier add multiply negate inverse)
  (forall (x y)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y))
     (and
      (q848375-member-p
       carrier (q848375-binary-value add x y))
      (q848375-member-p
       carrier (q848375-binary-value multiply x y))
      (q848375-member-p
       carrier (q848375-unary-value negate x))
      (q848375-member-p
       carrier (q848375-unary-value inverse x))))))

(defun-sk q848375-field-additive-laws-p
    (carrier add negate zero)
  (forall (x y z)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y)
      (q848375-member-p carrier z))
     (and
      (equal
       (q848375-binary-value
        add (q848375-binary-value add x y) z)
       (q848375-binary-value
        add x (q848375-binary-value add y z)))
      (equal
       (q848375-binary-value add x y)
       (q848375-binary-value add y x))
      (equal (q848375-binary-value add x zero) x)
      (equal
       (q848375-binary-value
        add x (q848375-unary-value negate x))
       zero)))))

(defun-sk q848375-field-multiplicative-laws-p
    (carrier multiply inverse zero one)
  (forall (x y z)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y)
      (q848375-member-p carrier z))
     (and
      (equal
       (q848375-binary-value
        multiply (q848375-binary-value multiply x y) z)
       (q848375-binary-value
        multiply x (q848375-binary-value multiply y z)))
      (equal
       (q848375-binary-value multiply x y)
       (q848375-binary-value multiply y x))
      (equal (q848375-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (q848375-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (q848375-binary-value
         multiply x (q848375-unary-value inverse x))
        one))))))

(defun-sk q848375-field-distributive-p
    (carrier add multiply)
  (forall (x y z)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y)
      (q848375-member-p carrier z))
      (equal
       (q848375-binary-value
        multiply x (q848375-binary-value add y z))
       (q848375-binary-value
        add
        (q848375-binary-value multiply x y)
        (q848375-binary-value multiply x z))))))

(defun-sk q848375-norm-cut-laws-p (carrier norm-lt zero)
  (forall (x q r)
    (implies
     (q848375-member-p carrier x)
     (and
      (implies
       (q848375-norm-lt-p norm-lt x q)
       (q848375-positive-rational-p q))
      (implies
       (and
        (q848375-norm-lt-p norm-lt x q)
        (rationalp r)
        (< q r))
       (q848375-norm-lt-p norm-lt x r))
      (implies
       (q848375-norm-lt-p norm-lt x q)
       (q848375-norm-rounded-p norm-lt x q))
      (q848375-norm-finite-p norm-lt x)
      (iff
       (equal x zero)
       (not (q848375-norm-positive-p norm-lt x)))))))

(defun-sk q848375-field-norm-zero-one-p (norm-lt zero one)
  (forall (q)
    (and
      (iff
       (q848375-norm-lt-p norm-lt zero q)
       (q848375-positive-rational-p q))
      (iff
       (q848375-norm-lt-p norm-lt one q)
       (and (rationalp q) (< 1 q))))))

(defun-sk q848375-field-norm-negate-p
    (carrier negate norm-lt)
  (forall (x q)
    (implies
     (q848375-member-p carrier x)
      (iff
       (q848375-norm-lt-p
        norm-lt (q848375-unary-value negate x) q)
       (q848375-norm-lt-p norm-lt x q)))))

(defun-sk q848375-field-norm-add-p
    (carrier add norm-lt)
  (forall (x y r s)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y))
      (implies
       (and
        (q848375-positive-rational-p r)
        (q848375-positive-rational-p s)
        (q848375-norm-lt-p norm-lt x r)
        (q848375-norm-lt-p norm-lt y s))
       (q848375-norm-lt-p
        norm-lt (q848375-binary-value add x y) (+ r s))))))

(defun-sk q848375-field-norm-multiply-p
    (carrier multiply norm-lt)
  (forall (x y q)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y))
      (iff
       (q848375-norm-lt-p
        norm-lt (q848375-binary-value multiply x y) q)
       (q848375-norm-product-lt-p
        norm-lt norm-lt x y q)))))

(defun q848375-nontrivially-normed-field-p
    (carrier add multiply negate inverse zero one norm-lt)
  (and
   (q848375-member-p carrier zero)
   (q848375-member-p carrier one)
   (not (equal zero one))
   (q848375-field-closure-p
    carrier add multiply negate inverse)
   (q848375-field-additive-laws-p carrier add negate zero)
   (q848375-field-multiplicative-laws-p
    carrier multiply inverse zero one)
   (q848375-field-distributive-p carrier add multiply)
   (q848375-norm-cut-laws-p carrier norm-lt zero)
   (q848375-field-norm-zero-one-p norm-lt zero one)
   (q848375-field-norm-negate-p carrier negate norm-lt)
   (q848375-field-norm-add-p carrier add norm-lt)
   (q848375-field-norm-multiply-p
    carrier multiply norm-lt)))

;; Normed vector spaces over the represented field.

(defun-sk q848375-space-closure-p
    (field-carrier carrier add negate scalar-multiply)
  (forall (a x y)
    (implies
     (and
      (q848375-member-p field-carrier a)
      (q848375-member-p carrier x)
      (q848375-member-p carrier y))
     (and
      (q848375-member-p
       carrier (q848375-binary-value add x y))
      (q848375-member-p
       carrier (q848375-unary-value negate x))
      (q848375-member-p
       carrier (q848375-binary-value scalar-multiply a x))
      ))))

(defun-sk q848375-space-additive-laws-p
    (carrier add negate zero)
  (forall (x y z)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y)
      (q848375-member-p carrier z))
     (and
      (equal
       (q848375-binary-value
        add (q848375-binary-value add x y) z)
       (q848375-binary-value
        add x (q848375-binary-value add y z)))
      (equal
       (q848375-binary-value add x y)
       (q848375-binary-value add y x))
      (equal (q848375-binary-value add x zero) x)
      (equal
       (q848375-binary-value
        add x (q848375-unary-value negate x))
       zero)))))

(defun-sk q848375-space-module-laws-p
    (field-carrier field-add field-multiply field-one
     carrier add scalar-multiply)
  (forall (a b x y)
    (implies
     (and
      (q848375-member-p field-carrier a)
      (q848375-member-p field-carrier b)
      (q848375-member-p carrier x)
      (q848375-member-p carrier y))
     (and
      (equal
       (q848375-binary-value scalar-multiply field-one x)
       x)
      (equal
       (q848375-binary-value
        scalar-multiply
        (q848375-binary-value field-multiply a b)
        x)
       (q848375-binary-value
        scalar-multiply
        a
        (q848375-binary-value scalar-multiply b x)))
      (equal
       (q848375-binary-value
        scalar-multiply
        (q848375-binary-value field-add a b)
        x)
       (q848375-binary-value
        add
        (q848375-binary-value scalar-multiply a x)
        (q848375-binary-value scalar-multiply b x)))
      (equal
       (q848375-binary-value
        scalar-multiply a (q848375-binary-value add x y))
       (q848375-binary-value
        add
        (q848375-binary-value scalar-multiply a x)
        (q848375-binary-value scalar-multiply a y)))
      ))))

(defun-sk q848375-space-norm-negate-p
    (carrier negate norm-lt)
  (forall (x q)
    (implies
     (q848375-member-p carrier x)
     (iff
      (q848375-norm-lt-p
       norm-lt (q848375-unary-value negate x) q)
      (q848375-norm-lt-p norm-lt x q)))))

(defun-sk q848375-space-norm-add-p
    (carrier add norm-lt)
  (forall (x y r s)
    (implies
     (and
      (q848375-member-p carrier x)
      (q848375-member-p carrier y))
     (implies
      (and
       (q848375-positive-rational-p r)
       (q848375-positive-rational-p s)
       (q848375-norm-lt-p norm-lt x r)
       (q848375-norm-lt-p norm-lt y s))
      (q848375-norm-lt-p
       norm-lt (q848375-binary-value add x y) (+ r s))))))

(defun-sk q848375-space-norm-smul-p
    (field-carrier field-norm-lt carrier scalar-multiply norm-lt)
  (forall (a x q)
    (implies
     (and
      (q848375-member-p field-carrier a)
      (q848375-member-p carrier x))
     (iff
      (q848375-norm-lt-p
       norm-lt
       (q848375-binary-value scalar-multiply a x)
       q)
      (q848375-norm-product-lt-p
       field-norm-lt norm-lt a x q)))))

(defun q848375-space-laws-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (and
   (q848375-space-closure-p
    field-carrier carrier add negate scalar-multiply)
   (q848375-space-additive-laws-p carrier add negate zero)
   (q848375-space-module-laws-p
    field-carrier field-add field-multiply field-one
    carrier add scalar-multiply)
   (q848375-norm-cut-laws-p carrier norm-lt zero)
   (q848375-space-norm-negate-p carrier negate norm-lt)
   (q848375-space-norm-add-p carrier add norm-lt)
   (q848375-space-norm-smul-p
    field-carrier field-norm-lt carrier scalar-multiply norm-lt)))

(defun q848375-normed-space-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (and
   (q848375-member-p carrier zero)
   (q848375-space-laws-p
    field-carrier field-add field-multiply field-one field-norm-lt
    carrier add negate zero scalar-multiply norm-lt)))

(defun q848375-vector-difference (add negate left right)
  (q848375-binary-value
   add left (q848375-unary-value negate right)))

;; Sequential completeness is equivalent to metric completeness here.

(defun-sk q848375-sequence-values-p (carrier sequence)
  (forall (index)
    (implies
     (natp index)
     (q848375-member-p
      carrier (q848375-unary-value sequence index)))))

(defun q848375-sequence-p (carrier sequence)
  (q848375-sequence-values-p carrier sequence))

(defun-sk q848375-cauchy-tail-p
    (carrier add negate norm-lt sequence epsilon start)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (natp start)
      (<= start left-index)
      (<= start right-index))
     (q848375-norm-lt-p
      norm-lt
      (q848375-vector-difference
       add negate
       (q848375-unary-value sequence left-index)
       (q848375-unary-value sequence right-index))
      epsilon))))

(defun-sk q848375-cauchy-start-exists-p
    (carrier add negate norm-lt sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q848375-cauchy-tail-p
      carrier add negate norm-lt sequence epsilon start))))

(defun-sk q848375-cauchy-p
    (carrier add negate norm-lt sequence)
  (forall (epsilon)
    (implies
     (q848375-positive-rational-p epsilon)
     (q848375-cauchy-start-exists-p
      carrier add negate norm-lt sequence epsilon))))

(defun-sk q848375-convergence-tail-p
    (carrier add negate norm-lt sequence limit epsilon start)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp start)
      (<= start index))
     (q848375-norm-lt-p
      norm-lt
      (q848375-vector-difference
       add negate
       (q848375-unary-value sequence index)
       limit)
      epsilon))))

(defun-sk q848375-convergence-start-exists-p
    (carrier add negate norm-lt sequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (q848375-convergence-tail-p
      carrier add negate norm-lt
      sequence limit epsilon start))))

(defun-sk q848375-converges-p
    (carrier add negate norm-lt sequence limit)
  (forall (epsilon)
    (implies
     (q848375-positive-rational-p epsilon)
     (q848375-convergence-start-exists-p
      carrier add negate norm-lt sequence limit epsilon))))

(defun-sk q848375-limit-exists-p
    (carrier add negate norm-lt sequence)
  (exists (limit)
    (and
     (q848375-member-p carrier limit)
     (q848375-converges-p
      carrier add negate norm-lt sequence limit))))

(defun-sk q848375-complete-space-p
    (carrier add negate norm-lt)
  (forall (sequence)
    (implies
     (and
      (q848375-sequence-p carrier sequence)
      (q848375-cauchy-p
       carrier add negate norm-lt sequence))
     (q848375-limit-exists-p
      carrier add negate norm-lt sequence))))

(defun q848375-banach-space-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (and
   (q848375-normed-space-p
    field-carrier field-add field-multiply field-one field-norm-lt
    carrier add negate zero scalar-multiply norm-lt)
   (q848375-complete-space-p carrier add negate norm-lt)))

;; Packed field, spaces, and the five fields of ImplicitFunctionData.

(defun q848375-field-carrier (field) (nth 0 field))
(defun q848375-field-add (field) (nth 1 field))
(defun q848375-field-multiply (field) (nth 2 field))
(defun q848375-field-negate (field) (nth 3 field))
(defun q848375-field-inverse (field) (nth 4 field))
(defun q848375-field-zero (field) (nth 5 field))
(defun q848375-field-one (field) (nth 6 field))
(defun q848375-field-norm-lt (field) (nth 7 field))

(defun q848375-space-carrier (space) (nth 0 space))
(defun q848375-space-add (space) (nth 1 space))
(defun q848375-space-negate (space) (nth 2 space))
(defun q848375-space-zero (space) (nth 3 space))
(defun q848375-space-smul (space) (nth 4 space))
(defun q848375-space-norm-lt (space) (nth 5 space))

(defun q848375-data-left-function (data) (nth 0 data))
(defun q848375-data-left-derivative (data) (nth 1 data))
(defun q848375-data-right-function (data) (nth 2 data))
(defun q848375-data-right-derivative (data) (nth 3 data))
(defun q848375-data-point (data) (nth 4 data))

(defun q848375-homeomorph-source (homeomorph) (nth 0 homeomorph))
(defun q848375-homeomorph-target (homeomorph) (nth 1 homeomorph))
(defun q848375-homeomorph-inverse (homeomorph) (nth 2 homeomorph))

(defun q848375-field-p (field)
  (and
   (true-listp field)
   (equal (len field) 8)
   (q848375-nontrivially-normed-field-p
    (q848375-field-carrier field)
    (q848375-field-add field)
    (q848375-field-multiply field)
    (q848375-field-negate field)
    (q848375-field-inverse field)
    (q848375-field-zero field)
    (q848375-field-one field)
    (q848375-field-norm-lt field))))

(defun q848375-banach-space-context-p (field space)
  (and
   (true-listp space)
   (equal (len space) 6)
   (q848375-banach-space-p
    (q848375-field-carrier field)
    (q848375-field-add field)
    (q848375-field-multiply field)
    (q848375-field-one field)
    (q848375-field-norm-lt field)
    (q848375-space-carrier space)
    (q848375-space-add space)
    (q848375-space-negate space)
    (q848375-space-zero space)
    (q848375-space-smul space)
    (q848375-space-norm-lt space))))

;; Typed functions and continuous linear maps.

(defun-sk q848375-function-values-p
    (domain-carrier codomain-carrier function)
  (forall (x)
    (implies
     (q848375-member-p domain-carrier x)
     (q848375-member-p
      codomain-carrier (q848375-unary-value function x)))))

(defun q848375-function-p
    (domain-carrier codomain-carrier function)
  (q848375-function-values-p
   domain-carrier codomain-carrier function))

(defun-sk q848375-binary-function-values-p
    (left-carrier right-carrier codomain-carrier function)
  (forall (left right)
    (implies
     (and
      (q848375-member-p left-carrier left)
      (q848375-member-p right-carrier right))
     (q848375-member-p
      codomain-carrier
      (q848375-binary-value function left right)))))

(defun q848375-binary-function-p
    (left-carrier right-carrier codomain-carrier function)
  (q848375-binary-function-values-p
   left-carrier right-carrier codomain-carrier function))

(defun-sk q848375-linear-map-laws-p
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add domain-smul codomain-smul mapping)
  (forall (scalar left right)
    (implies
     (and
      (q848375-member-p field-carrier scalar)
      (q848375-member-p domain-carrier left)
      (q848375-member-p domain-carrier right))
     (and
      (q848375-member-p
       codomain-carrier (q848375-unary-value mapping left))
      (equal
       (q848375-unary-value
        mapping (q848375-binary-value domain-add left right))
       (q848375-binary-value
        codomain-add
        (q848375-unary-value mapping left)
        (q848375-unary-value mapping right)))
      (equal
       (q848375-unary-value
        mapping (q848375-binary-value domain-smul scalar left))
       (q848375-binary-value
        codomain-smul scalar
        (q848375-unary-value mapping left)))))))

(defun q848375-linear-map-p
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add domain-smul codomain-smul mapping)
  (q848375-linear-map-laws-p
   field-carrier domain-carrier codomain-carrier
   domain-add codomain-add domain-smul codomain-smul mapping))

(defun-sk q848375-continuity-at-zero-delta-p
    (domain-space codomain-space mapping epsilon delta)
  (forall (x)
    (implies
     (and
      (q848375-member-p
       (q848375-space-carrier domain-space) x)
      (q848375-norm-lt-p
       (q848375-space-norm-lt domain-space) x delta))
     (q848375-norm-lt-p
      (q848375-space-norm-lt codomain-space)
      (q848375-unary-value mapping x)
      epsilon))))

(defun-sk q848375-continuity-at-zero-delta-exists-p
    (domain-space codomain-space mapping epsilon)
  (exists (delta)
    (and
     (q848375-positive-rational-p delta)
     (q848375-continuity-at-zero-delta-p
      domain-space codomain-space mapping epsilon delta))))

(defun-sk q848375-continuous-at-zero-p
    (domain-space codomain-space mapping)
  (forall (epsilon)
    (implies
     (q848375-positive-rational-p epsilon)
     (q848375-continuity-at-zero-delta-exists-p
      domain-space codomain-space mapping epsilon))))

(defun q848375-continuous-linear-map-p
    (field domain-space codomain-space mapping)
  (and
   (q848375-linear-map-p
    (q848375-field-carrier field)
    (q848375-space-carrier domain-space)
    (q848375-space-carrier codomain-space)
    (q848375-space-add domain-space)
    (q848375-space-add codomain-space)
    (q848375-space-smul domain-space)
    (q848375-space-smul codomain-space)
    mapping)
   (q848375-continuous-at-zero-p
    domain-space codomain-space mapping)))

;; Exact upper-cut form of A <= epsilon * B.

(defun-sk q848375-scaled-norm-bound-p
    (codomain-norm-lt remainder domain-norm-lt increment epsilon)
  (forall (domain-bound codomain-bound)
    (implies
     (and
      (q848375-positive-rational-p domain-bound)
      (q848375-positive-rational-p codomain-bound)
      (q848375-norm-lt-p
       domain-norm-lt increment domain-bound)
      (< (* epsilon domain-bound) codomain-bound))
     (q848375-norm-lt-p
      codomain-norm-lt remainder codomain-bound))))

(defun-sk q848375-strict-derivative-points-p
    (domain-space codomain-space function derivative
     point epsilon radius)
  (forall (x y)
    (implies
     (and
      (q848375-member-p
       (q848375-space-carrier domain-space) x)
      (q848375-member-p
       (q848375-space-carrier domain-space) y)
      (q848375-norm-lt-p
       (q848375-space-norm-lt domain-space)
       (q848375-vector-difference
        (q848375-space-add domain-space)
        (q848375-space-negate domain-space)
        x point)
       radius)
      (q848375-norm-lt-p
       (q848375-space-norm-lt domain-space)
       (q848375-vector-difference
        (q848375-space-add domain-space)
        (q848375-space-negate domain-space)
        y point)
       radius))
     (q848375-scaled-norm-bound-p
      (q848375-space-norm-lt codomain-space)
      (q848375-vector-difference
       (q848375-space-add codomain-space)
       (q848375-space-negate codomain-space)
       (q848375-vector-difference
        (q848375-space-add codomain-space)
        (q848375-space-negate codomain-space)
        (q848375-unary-value function x)
        (q848375-unary-value function y))
       (q848375-unary-value
        derivative
        (q848375-vector-difference
         (q848375-space-add domain-space)
         (q848375-space-negate domain-space)
         x y)))
      (q848375-space-norm-lt domain-space)
      (q848375-vector-difference
       (q848375-space-add domain-space)
       (q848375-space-negate domain-space)
       x y)
      epsilon))))

(defun-sk q848375-strict-derivative-radius-exists-p
    (domain-space codomain-space function derivative point epsilon)
  (exists (radius)
    (and
     (q848375-positive-rational-p radius)
     (q848375-strict-derivative-points-p
      domain-space codomain-space function derivative
      point epsilon radius))))

(defun-sk q848375-has-strict-fderiv-at-p
    (domain-space codomain-space function derivative point)
  (forall (epsilon)
    (implies
     (q848375-positive-rational-p epsilon)
     (q848375-strict-derivative-radius-exists-p
      domain-space codomain-space function derivative
      point epsilon))))

(defun q848375-strict-derivative-data-p
    (domain-space codomain-space function derivative point)
  (and
   (q848375-function-p
    (q848375-space-carrier domain-space)
    (q848375-space-carrier codomain-space)
    function)
   (q848375-has-strict-fderiv-at-p
    domain-space codomain-space function derivative point)))

;; Surjectivity and complementary derivative kernels.

(defun-sk q848375-preimage-exists-p
    (domain-carrier mapping target)
  (exists (preimage)
    (and
     (q848375-member-p domain-carrier preimage)
     (equal (q848375-unary-value mapping preimage) target))))

(defun-sk q848375-surjective-p
    (domain-carrier codomain-carrier mapping)
  (forall (target)
    (implies
     (q848375-member-p codomain-carrier target)
     (q848375-preimage-exists-p
      domain-carrier mapping target))))

(defun-sk q848375-kernel-intersection-trivial-p
    (domain-space left-space right-space left-map right-map)
  (forall (x)
    (implies
     (and
      (q848375-member-p
       (q848375-space-carrier domain-space) x)
      (equal
       (q848375-unary-value left-map x)
       (q848375-space-zero left-space))
      (equal
       (q848375-unary-value right-map x)
       (q848375-space-zero right-space)))
     (equal x (q848375-space-zero domain-space)))))

(defun-sk q848375-kernel-decomposition-exists-p
    (domain-space left-space right-space left-map right-map x)
  (exists (left-part right-part)
    (and
     (q848375-member-p
      (q848375-space-carrier domain-space) left-part)
     (q848375-member-p
      (q848375-space-carrier domain-space) right-part)
     (equal
      (q848375-unary-value left-map left-part)
      (q848375-space-zero left-space))
     (equal
      (q848375-unary-value right-map right-part)
      (q848375-space-zero right-space))
     (equal
      (q848375-binary-value
       (q848375-space-add domain-space)
       left-part right-part)
      x))))

(defun-sk q848375-kernel-decomposition-p
    (domain-space left-space right-space left-map right-map)
  (forall (x)
    (implies
     (q848375-member-p
      (q848375-space-carrier domain-space) x)
     (q848375-kernel-decomposition-exists-p
      domain-space left-space right-space left-map right-map x))))

(defun q848375-complementary-kernels-p
    (domain-space left-space right-space left-map right-map)
  (and
   (q848375-kernel-intersection-trivial-p
    domain-space left-space right-space left-map right-map)
   (q848375-kernel-decomposition-p
    domain-space left-space right-space left-map right-map)))

(defun q848375-implicit-function-data-p
    (field domain-space left-space right-space data)
  (and
   (q848375-field-p field)
   (q848375-banach-space-context-p field domain-space)
   (q848375-banach-space-context-p field left-space)
   (q848375-banach-space-context-p field right-space)
   (true-listp data)
   (equal (len data) 5)
   (q848375-member-p
    (q848375-space-carrier domain-space)
    (q848375-data-point data))
   (q848375-continuous-linear-map-p
    field domain-space left-space
    (q848375-data-left-derivative data))
   (q848375-continuous-linear-map-p
    field domain-space right-space
    (q848375-data-right-derivative data))
   (q848375-strict-derivative-data-p
    domain-space left-space
    (q848375-data-left-function data)
    (q848375-data-left-derivative data)
    (q848375-data-point data))
   (q848375-strict-derivative-data-p
    domain-space right-space
    (q848375-data-right-function data)
    (q848375-data-right-derivative data)
    (q848375-data-point data))
   (q848375-surjective-p
    (q848375-space-carrier domain-space)
    (q848375-space-carrier left-space)
    (q848375-data-left-derivative data))
   (q848375-surjective-p
    (q848375-space-carrier domain-space)
    (q848375-space-carrier right-space)
    (q848375-data-right-derivative data))
   (q848375-complementary-kernels-p
    domain-space left-space right-space
    (q848375-data-left-derivative data)
    (q848375-data-right-derivative data))))

;; Open sets in the norm topologies, including the max-norm product topology.

(defun-sk q848375-set-members-carrier-p (carrier set)
  (forall (x)
    (implies
     (q848375-member-p set x)
     (q848375-member-p carrier x))))

(defun q848375-valid-set-p (carrier set)
  (q848375-set-members-carrier-p carrier set))

(defun-sk q848375-ball-subset-p
    (space set center radius)
  (forall (x)
    (implies
     (and
      (q848375-member-p (q848375-space-carrier space) x)
      (q848375-norm-lt-p
       (q848375-space-norm-lt space)
       (q848375-vector-difference
        (q848375-space-add space)
        (q848375-space-negate space)
        x center)
       radius))
     (q848375-member-p set x))))

(defun-sk q848375-open-radius-exists-p (space set center)
  (exists (radius)
    (and
     (q848375-positive-rational-p radius)
     (q848375-ball-subset-p space set center radius))))

(defun-sk q848375-open-at-every-point-p (space set)
  (forall (center)
    (implies
     (q848375-member-p set center)
     (q848375-open-radius-exists-p space set center))))

(defun q848375-open-set-p (space set)
  (and
   (q848375-valid-set-p
    (q848375-space-carrier space) set)
   (q848375-open-at-every-point-p space set)))

(defun q848375-product-member-p
    (left-space right-space pair)
  (and
   (consp pair)
   (q848375-member-p
    (q848375-space-carrier left-space) (car pair))
   (q848375-member-p
    (q848375-space-carrier right-space) (cdr pair))))

(defun-sk q848375-product-set-valid-p
    (left-space right-space set)
  (forall (pair)
    (implies
     (q848375-member-p set pair)
     (q848375-product-member-p
      left-space right-space pair))))

(defun-sk q848375-product-ball-subset-p
    (left-space right-space set center radius)
  (forall (pair)
    (implies
     (and
      (q848375-product-member-p left-space right-space pair)
      (q848375-norm-lt-p
       (q848375-space-norm-lt left-space)
       (q848375-vector-difference
        (q848375-space-add left-space)
        (q848375-space-negate left-space)
        (car pair) (car center))
       radius)
      (q848375-norm-lt-p
       (q848375-space-norm-lt right-space)
       (q848375-vector-difference
        (q848375-space-add right-space)
        (q848375-space-negate right-space)
        (cdr pair) (cdr center))
       radius))
     (q848375-member-p set pair))))

(defun-sk q848375-product-open-radius-exists-p
    (left-space right-space set center)
  (exists (radius)
    (and
     (q848375-positive-rational-p radius)
     (q848375-product-ball-subset-p
      left-space right-space set center radius))))

(defun-sk q848375-product-open-at-every-point-p
    (left-space right-space set)
  (forall (center)
    (implies
     (q848375-member-p set center)
     (q848375-product-open-radius-exists-p
      left-space right-space set center))))

(defun q848375-product-open-set-p
    (left-space right-space set)
  (and
   (q848375-product-set-valid-p left-space right-space set)
   (q848375-product-open-at-every-point-p
    left-space right-space set)))

;; The exact forward map x |-> (leftFun x, rightFun x).

(defun q848375-forward-value (data x)
  (cons
   (q848375-unary-value
    (q848375-data-left-function data) x)
   (q848375-unary-value
    (q848375-data-right-function data) x)))

(defun-sk q848375-forward-maps-source-p
    (data source target)
  (forall (x)
    (implies
     (q848375-member-p source x)
     (q848375-member-p
      target (q848375-forward-value data x)))))

(defun-sk q848375-inverse-values-p
    (domain-space left-space right-space inverse)
  (forall (pair)
    (implies
     (q848375-product-member-p left-space right-space pair)
     (q848375-member-p
      (q848375-space-carrier domain-space)
      (q848375-unary-value inverse pair)))))

(defun-sk q848375-inverse-maps-target-p
    (source target inverse)
  (forall (pair)
    (implies
     (q848375-member-p target pair)
     (q848375-member-p
      source (q848375-unary-value inverse pair)))))

(defun-sk q848375-left-inverse-on-source-p
    (data source inverse)
  (forall (x)
    (implies
     (q848375-member-p source x)
     (equal
      (q848375-unary-value
       inverse (q848375-forward-value data x))
      x))))

(defun-sk q848375-right-inverse-on-target-p
    (data target inverse)
  (forall (pair)
    (implies
     (q848375-member-p target pair)
     (equal
      (q848375-forward-value
       data (q848375-unary-value inverse pair))
      pair))))

;; Relative continuity on source and target.

(defun-sk q848375-forward-continuity-delta-p
    (domain-space left-space right-space data source
     center epsilon delta)
  (forall (x)
    (implies
     (and
      (q848375-member-p source x)
      (q848375-norm-lt-p
       (q848375-space-norm-lt domain-space)
       (q848375-vector-difference
        (q848375-space-add domain-space)
        (q848375-space-negate domain-space)
        x center)
       delta))
     (and
      (q848375-norm-lt-p
       (q848375-space-norm-lt left-space)
       (q848375-vector-difference
        (q848375-space-add left-space)
        (q848375-space-negate left-space)
        (q848375-unary-value
         (q848375-data-left-function data) x)
        (q848375-unary-value
         (q848375-data-left-function data) center))
       epsilon)
      (q848375-norm-lt-p
       (q848375-space-norm-lt right-space)
       (q848375-vector-difference
        (q848375-space-add right-space)
        (q848375-space-negate right-space)
        (q848375-unary-value
         (q848375-data-right-function data) x)
        (q848375-unary-value
         (q848375-data-right-function data) center))
       epsilon)))))

(defun-sk q848375-forward-continuity-delta-exists-p
    (domain-space left-space right-space data source center epsilon)
  (exists (delta)
    (and
     (q848375-positive-rational-p delta)
     (q848375-forward-continuity-delta-p
      domain-space left-space right-space data source
      center epsilon delta))))

(defun-sk q848375-forward-continuous-at-p
    (domain-space left-space right-space data source center)
  (forall (epsilon)
    (implies
     (q848375-positive-rational-p epsilon)
     (q848375-forward-continuity-delta-exists-p
      domain-space left-space right-space data source
      center epsilon))))

(defun-sk q848375-forward-continuous-on-source-p
    (domain-space left-space right-space data source)
  (forall (center)
    (implies
     (q848375-member-p source center)
     (q848375-forward-continuous-at-p
      domain-space left-space right-space data source center))))

(defun-sk q848375-inverse-continuity-delta-p
    (domain-space left-space right-space target inverse
     center epsilon delta)
  (forall (pair)
    (implies
     (and
      (q848375-member-p target pair)
      (q848375-norm-lt-p
       (q848375-space-norm-lt left-space)
       (q848375-vector-difference
        (q848375-space-add left-space)
        (q848375-space-negate left-space)
        (car pair) (car center))
       delta)
      (q848375-norm-lt-p
       (q848375-space-norm-lt right-space)
       (q848375-vector-difference
        (q848375-space-add right-space)
        (q848375-space-negate right-space)
        (cdr pair) (cdr center))
       delta))
     (q848375-norm-lt-p
      (q848375-space-norm-lt domain-space)
      (q848375-vector-difference
       (q848375-space-add domain-space)
       (q848375-space-negate domain-space)
       (q848375-unary-value inverse pair)
       (q848375-unary-value inverse center))
      epsilon))))

(defun-sk q848375-inverse-continuity-delta-exists-p
    (domain-space left-space right-space target inverse center epsilon)
  (exists (delta)
    (and
     (q848375-positive-rational-p delta)
     (q848375-inverse-continuity-delta-p
      domain-space left-space right-space target inverse
      center epsilon delta))))

(defun-sk q848375-inverse-continuous-at-p
    (domain-space left-space right-space target inverse center)
  (forall (epsilon)
    (implies
     (q848375-positive-rational-p epsilon)
     (q848375-inverse-continuity-delta-exists-p
      domain-space left-space right-space target inverse
      center epsilon))))

(defun-sk q848375-inverse-continuous-on-target-p
    (domain-space left-space right-space target inverse)
  (forall (center)
    (implies
     (q848375-member-p target center)
     (q848375-inverse-continuous-at-p
      domain-space left-space right-space target inverse center))))

(defun q848375-open-partial-homeomorph-p
    (domain-space left-space right-space data homeomorph)
  (let ((source (q848375-homeomorph-source homeomorph))
        (target (q848375-homeomorph-target homeomorph))
        (inverse (q848375-homeomorph-inverse homeomorph)))
    (and
     (true-listp homeomorph)
     (equal (len homeomorph) 3)
     (q848375-open-set-p domain-space source)
     (q848375-product-open-set-p
      left-space right-space target)
     (q848375-inverse-values-p
      domain-space left-space right-space inverse)
     (q848375-member-p source (q848375-data-point data))
     (q848375-forward-maps-source-p data source target)
     (q848375-inverse-maps-target-p source target inverse)
     (q848375-left-inverse-on-source-p data source inverse)
     (q848375-right-inverse-on-target-p data target inverse)
     (q848375-forward-continuous-on-source-p
      domain-space left-space right-space data source)
     (q848375-inverse-continuous-on-target-p
      domain-space left-space right-space target inverse))))

;; The derivative of prodFun is x |-> (leftDeriv x, rightDeriv x). Under the
;; ImplicitFunctionData assumptions it is bijective, so this choice is unique.

(defun-sk q848375-combined-derivative-preimage-exists-p
    (domain-space left-space right-space data pair)
  (exists (preimage)
    (and
     (q848375-member-p
      (q848375-space-carrier domain-space) preimage)
     (equal
      (q848375-unary-value
       (q848375-data-left-derivative data) preimage)
      (car pair))
     (equal
      (q848375-unary-value
       (q848375-data-right-derivative data) preimage)
      (cdr pair)))))

(defchoose q848375-combined-derivative-inverse-value
    (preimage)
    (domain-space left-space right-space data pair)
  (and
   (q848375-member-p
    (q848375-space-carrier domain-space) preimage)
   (equal
    (q848375-unary-value
     (q848375-data-left-derivative data) preimage)
    (car pair))
   (equal
    (q848375-unary-value
     (q848375-data-right-derivative data) preimage)
    (cdr pair))))

(defun q848375-rational-max (left right)
  (if (< left right) right left))

;; Exact rational upper cut of the operator norm of the inverse combined
;; derivative. The product space uses its max norm.

(defun-sk q848375-combined-inverse-bound-p
    (domain-space left-space right-space data coefficient)
  (forall (left right left-bound right-bound output-bound)
    (implies
     (and
      (q848375-positive-rational-p coefficient)
      (q848375-product-member-p left-space right-space
                               (cons left right))
      (q848375-positive-rational-p left-bound)
      (q848375-positive-rational-p right-bound)
      (q848375-positive-rational-p output-bound)
      (q848375-norm-lt-p
       (q848375-space-norm-lt left-space) left left-bound)
      (q848375-norm-lt-p
       (q848375-space-norm-lt right-space) right right-bound)
      (<
       (* coefficient
          (q848375-rational-max left-bound right-bound))
       output-bound))
     (q848375-norm-lt-p
      (q848375-space-norm-lt domain-space)
      (q848375-combined-derivative-inverse-value
       domain-space left-space right-space data
       (cons left right))
      output-bound))))

(defun-sk q848375-combined-inverse-operator-norm-lt-p
    (domain-space left-space right-space data bound)
  (exists (coefficient)
    (and
     (q848375-positive-rational-p bound)
     (q848375-positive-rational-p coefficient)
     (< coefficient bound)
     (q848375-combined-inverse-bound-p
      domain-space left-space right-space data coefficient))))

(defun-sk q848375-combined-inverse-operator-norm-positive-p
    (domain-space left-space right-space data)
  (exists (bound)
    (and
     (q848375-positive-rational-p bound)
     (not
      (q848375-combined-inverse-operator-norm-lt-p
       domain-space left-space right-space data bound)))))

(defun-sk q848375-combined-inverse-operator-norm-greater-p
    (domain-space left-space right-space data threshold)
  (exists (bound)
    (and
     (q848375-positive-rational-p threshold)
     (q848375-positive-rational-p bound)
     (< threshold bound)
     (not
      (q848375-combined-inverse-operator-norm-lt-p
       domain-space left-space right-space data bound)))))

;; This is the strict upper-cut relation
;; ||combinedDerivative.symm||_+^{-1} / 2 < epsilon.

(defun q848375-half-inverse-operator-norm-lt-p
    (domain-space left-space right-space data epsilon)
  (and
   (q848375-positive-rational-p epsilon)
   (or
    (not
     (q848375-combined-inverse-operator-norm-positive-p
      domain-space left-space right-space data))
    (q848375-combined-inverse-operator-norm-greater-p
     domain-space left-space right-space data
     (/ 1 (* 2 epsilon))))))

(defun q848375-left-derivative-remainder
    (domain-space left-space data x y)
  (q848375-vector-difference
   (q848375-space-add left-space)
   (q848375-space-negate left-space)
   (q848375-vector-difference
    (q848375-space-add left-space)
    (q848375-space-negate left-space)
    (q848375-unary-value
     (q848375-data-left-function data) x)
    (q848375-unary-value
     (q848375-data-left-function data) y))
   (q848375-unary-value
    (q848375-data-left-derivative data)
    (q848375-vector-difference
     (q848375-space-add domain-space)
     (q848375-space-negate domain-space)
     x y))))

(defun q848375-right-derivative-remainder
    (domain-space right-space data x y)
  (q848375-vector-difference
   (q848375-space-add right-space)
   (q848375-space-negate right-space)
   (q848375-vector-difference
    (q848375-space-add right-space)
    (q848375-space-negate right-space)
    (q848375-unary-value
     (q848375-data-right-function data) x)
    (q848375-unary-value
     (q848375-data-right-function data) y))
   (q848375-unary-value
    (q848375-data-right-derivative data)
    (q848375-vector-difference
     (q848375-space-add domain-space)
     (q848375-space-negate domain-space)
     x y))))

;; This is ApproximatesLinearOn prodFun combinedDerivative source
;; (||combinedDerivative.symm||_+^{-1} / 2), expressed through rational cuts.

(defun-sk q848375-approximates-combined-derivative-on-p
    (domain-space left-space right-space data source)
  (forall (x y epsilon)
    (implies
     (and
      (q848375-member-p source x)
      (q848375-member-p source y)
      (q848375-half-inverse-operator-norm-lt-p
       domain-space left-space right-space data epsilon))
     (and
      (q848375-scaled-norm-bound-p
       (q848375-space-norm-lt left-space)
       (q848375-left-derivative-remainder
        domain-space left-space data x y)
       (q848375-space-norm-lt domain-space)
       (q848375-vector-difference
        (q848375-space-add domain-space)
        (q848375-space-negate domain-space)
        x y)
       epsilon)
      (q848375-scaled-norm-bound-p
       (q848375-space-norm-lt right-space)
       (q848375-right-derivative-remainder
        domain-space right-space data x y)
       (q848375-space-norm-lt domain-space)
       (q848375-vector-difference
        (q848375-space-add domain-space)
        (q848375-space-negate domain-space)
        x y)
       epsilon)))))

;; HasStrictFDerivAt.approximates_deriv_on_open_nhds proves existence of
;; exactly this predicate; Lean's toOpenPartialHomeomorph chooses its source
;; from that existential.

(defun q848375-derived-source-candidate-p
    (domain-space left-space right-space data source)
  (and
   (q848375-member-p source (q848375-data-point data))
   (q848375-open-set-p domain-space source)
   (q848375-approximates-combined-derivative-on-p
    domain-space left-space right-space data source)))

(defchoose q848375-derived-source
    (source)
    (domain-space left-space right-space data)
  (q848375-derived-source-candidate-p
   domain-space left-space right-space data source))

;; Set.InjOn.toPartialEquiv uses Function.invFunOn. Its inverse chooses the
;; unique source preimage when one exists and otherwise returns Classical.choice
;; of the nonempty domain. These choices make symm a total function.

(defun-sk q848375-source-preimage-exists-p
    (domain-space data source pair)
  (exists (preimage)
    (and
     (q848375-member-p
      (q848375-space-carrier domain-space) preimage)
     (q848375-member-p source preimage)
     (equal (q848375-forward-value data preimage) pair))))

(defchoose q848375-source-preimage
    (preimage)
    (domain-space data source pair)
  (and
   (q848375-member-p
    (q848375-space-carrier domain-space) preimage)
   (q848375-member-p source preimage)
   (equal (q848375-forward-value data preimage) pair)))

(defchoose q848375-carrier-default
    (element)
    (carrier)
  (q848375-member-p carrier element))

(defun q848375-derived-open-partial-homeomorph-symm
    (domain-space left-space right-space data pair)
  (let ((source
         (q848375-derived-source
          domain-space left-space right-space data)))
    (if
     (q848375-source-preimage-exists-p
      domain-space data source pair)
     (q848375-source-preimage
      domain-space data source pair)
     (q848375-carrier-default
      (q848375-space-carrier domain-space)))))

;; Pointwise equality on every typed pair is the uncurried form of Lean's
;; Function.curry. The inverse is kept as an explicit function object so the
;; final statement can connect the curried function to a local homeomorphism,
;; rather than merely restating the graph of a chosen total inverse.

(defun-sk q848375-implicit-function-is-curried-inverse-p
    (left-space right-space inverse implicit-function)
  (forall (left right)
    (implies
     (and
      (q848375-member-p
       (q848375-space-carrier left-space) left)
      (q848375-member-p
      (q848375-space-carrier right-space) right))
     (equal
      (q848375-binary-value implicit-function left right)
      (q848375-unary-value inverse (cons left right))))))

(defun-sk q848375-local-implicit-function-exists-p
    (field domain-space left-space right-space data implicit-function)
  (exists (homeomorph)
    (and
     (q848375-open-partial-homeomorph-p
      domain-space left-space right-space data homeomorph)
     (q848375-binary-function-p
      (q848375-space-carrier left-space)
      (q848375-space-carrier right-space)
      (q848375-space-carrier domain-space)
      implicit-function)
     (q848375-implicit-function-is-curried-inverse-p
      left-space right-space
      (q848375-homeomorph-inverse homeomorph)
      implicit-function))))

(defun thousand-theorems-q848375-implicit-function-statement
    (field domain-space left-space right-space data implicit-function)
  (implies
   (q848375-implicit-function-data-p
    field domain-space left-space right-space data)
   (q848375-local-implicit-function-exists-p
    field domain-space left-space right-space data
    implicit-function)))

(value-triple :itpeval-statement-checked)
:q
