;; Statement-only formalization of thousand-theorems corpus artifact Q7525341,
;; "Sion's minimax theorem": lower-semicontinuous quasiconvex sections on a
;; nonempty compact set and upper-semicontinuous quasiconcave sections on a
;; convex set have equal iterated infimum-supremum and supremum-infimum when
;; the displayed greatest and least bounds exist. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Tame APPLY$ functions represent arbitrary carriers, subsets, operations,
;; topologies, and the source function.  All algebraic, order, topological,
;; compactness, continuity, convexity, and bound conditions are explicit
;; hypotheses of the final predicate.

(defun q7525341-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q7525341-binary-relation-p (relation left right)
  (if (apply$ relation (list left right)) t nil))

(defun q7525341-unary-value (function argument)
  (apply$ function (list argument)))

(defun q7525341-binary-value (function left right)
  (apply$ function (list left right)))

;; Extensional subsets, families of subsets, and topologies.

(defun-sk q7525341-set-contained-p (carrier set)
  (forall (x)
    (implies
     (q7525341-member-p set x)
     (q7525341-member-p carrier x))))

(defun q7525341-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q7525341-set-contained-p carrier set)))

(defun-sk q7525341-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (iff
      (q7525341-member-p left x)
      (q7525341-member-p right x)))))

(defun-sk q7525341-family-extensional-p (carrier family)
  (forall (left right)
    (implies
     (and
      (q7525341-valid-set-p carrier left)
      (q7525341-valid-set-p carrier right)
      (q7525341-set-equiv-p carrier left right))
     (iff
      (q7525341-member-p family left)
      (q7525341-member-p family right)))))

(defun-sk q7525341-family-members-valid-p (carrier family)
  (forall (set)
    (implies
     (q7525341-member-p family set)
     (q7525341-valid-set-p carrier set))))

(defun q7525341-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q7525341-family-extensional-p carrier family)
   (q7525341-family-members-valid-p carrier family)))

(defun-sk q7525341-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (q7525341-member-p carrier x)
     (q7525341-member-p set x))))

(defun q7525341-open-set-p (carrier topology set)
  (and
   (q7525341-valid-set-p carrier set)
   (q7525341-member-p topology set)))

(defun-sk q7525341-empty-set-p (carrier set)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (not (q7525341-member-p set x)))))

(defun-sk q7525341-empty-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q7525341-valid-set-p carrier set)
     (q7525341-empty-set-p carrier set)
     (q7525341-open-set-p carrier topology set))))

(defun-sk q7525341-full-set-p (carrier set)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (q7525341-member-p set x))))

(defun-sk q7525341-full-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q7525341-valid-set-p carrier set)
     (q7525341-full-set-p carrier set)
     (q7525341-open-set-p carrier topology set))))

(defun-sk q7525341-intersection-representation-p
    (carrier left right intersection)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (iff
      (q7525341-member-p intersection x)
      (and
       (q7525341-member-p left x)
       (q7525341-member-p right x))))))

(defun-sk q7525341-open-intersection-exists-p
    (carrier topology left right)
  (exists (intersection)
    (and
     (q7525341-valid-set-p carrier intersection)
     (q7525341-intersection-representation-p
      carrier left right intersection)
     (q7525341-open-set-p carrier topology intersection))))

(defun-sk q7525341-topology-intersection-law-p
    (carrier topology)
  (forall (left right)
    (implies
     (and
      (q7525341-open-set-p carrier topology left)
      (q7525341-open-set-p carrier topology right))
     (q7525341-open-intersection-exists-p
      carrier topology left right))))

(defun-sk q7525341-union-member-p (carrier family x)
  (exists (set)
    (and
     (q7525341-valid-set-p carrier set)
     (q7525341-member-p family set)
     (q7525341-member-p set x))))

(defun-sk q7525341-union-representation-p
    (carrier family union)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (iff
      (q7525341-member-p union x)
      (q7525341-union-member-p carrier family x)))))

(defun-sk q7525341-family-members-open-p
    (carrier topology family)
  (forall (set)
    (implies
     (q7525341-member-p family set)
     (q7525341-open-set-p carrier topology set))))

(defun-sk q7525341-open-union-exists-p
    (carrier topology family)
  (exists (union)
    (and
     (q7525341-valid-set-p carrier union)
     (q7525341-union-representation-p carrier family union)
     (q7525341-open-set-p carrier topology union))))

(defun-sk q7525341-topology-union-law-p
    (carrier topology)
  (forall (family)
    (implies
     (and
      (q7525341-family-of-sets-p carrier family)
      (q7525341-family-members-open-p
       carrier topology family))
     (q7525341-open-union-exists-p
      carrier topology family))))

(defun q7525341-topological-space-p (carrier topology)
  (and
   (tamep-functionp carrier)
   (q7525341-family-of-sets-p carrier topology)
   (q7525341-empty-open-exists-p carrier topology)
   (q7525341-full-open-exists-p carrier topology)
   (q7525341-topology-intersection-law-p carrier topology)
   (q7525341-topology-union-law-p carrier topology)))

(defun-sk q7525341-complement-representation-p
    (carrier set complement)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (iff
      (q7525341-member-p complement x)
      (not (q7525341-member-p set x))))))

(defun-sk q7525341-open-complement-exists-p
    (carrier topology set)
  (exists (complement)
    (and
     (q7525341-valid-set-p carrier complement)
     (q7525341-complement-representation-p
      carrier set complement)
     (q7525341-open-set-p carrier topology complement))))

(defun q7525341-closed-set-p (carrier topology set)
  (and
   (q7525341-valid-set-p carrier set)
   (q7525341-open-complement-exists-p
    carrier topology set)))

;; Compactness by arbitrary open covers and internal finite subcovers.

(defun-sk q7525341-cover-point-p
    (carrier cover point)
  (exists (set)
    (and
     (q7525341-valid-set-p carrier set)
     (q7525341-member-p cover set)
     (q7525341-member-p set point))))

(defun-sk q7525341-cover-covers-set-p
    (carrier cover set)
  (forall (x)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p set x))
     (q7525341-cover-point-p carrier cover x))))

(defun q7525341-open-cover-p
    (carrier topology cover set)
  (and
   (q7525341-family-of-sets-p carrier cover)
   (q7525341-family-members-open-p carrier topology cover)
   (q7525341-cover-covers-set-p carrier cover set)))

(defun q7525341-subcover-list-p
    (carrier topology cover sets)
  (if (consp sets)
      (and
       (q7525341-open-set-p carrier topology (car sets))
       (q7525341-member-p cover (car sets))
       (q7525341-subcover-list-p
        carrier topology cover (cdr sets)))
    (equal sets nil)))

(defun q7525341-point-covered-by-list-p (sets point)
  (if (consp sets)
      (or
       (q7525341-member-p (car sets) point)
       (q7525341-point-covered-by-list-p (cdr sets) point))
    nil))

(defun-sk q7525341-list-covers-set-p
    (carrier sets set)
  (forall (x)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p set x))
     (q7525341-point-covered-by-list-p sets x))))

(defun-sk q7525341-finite-subcover-exists-p
    (carrier topology cover set)
  (exists (sets)
    (and
     (true-listp sets)
     (q7525341-subcover-list-p
      carrier topology cover sets)
     (q7525341-list-covers-set-p carrier sets set))))

(defun-sk q7525341-compact-set-p
    (carrier topology set)
  (forall (cover)
    (implies
     (q7525341-open-cover-p carrier topology cover set)
     (q7525341-finite-subcover-exists-p
      carrier topology cover set))))

;; The scalar field is a Dedekind-complete ordered field, hence a presentation
;; of the real numbers.  Its topology is constrained below to be the order
;; topology rather than an independently chosen topology.

(defun-sk q7525341-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p carrier z))
     (let* ((xy-add (q7525341-binary-value add x y))
            (yz-add (q7525341-binary-value add y z))
            (xy-mul (q7525341-binary-value multiply x y))
            (yz-mul (q7525341-binary-value multiply y z))
            (neg-x (q7525341-unary-value negate x))
            (inv-x (q7525341-unary-value inverse x)))
       (and
        (q7525341-member-p carrier xy-add)
        (q7525341-member-p carrier xy-mul)
        (q7525341-member-p carrier neg-x)
        (q7525341-member-p carrier inv-x)
        (equal
         (q7525341-binary-value add xy-add z)
         (q7525341-binary-value add x yz-add))
        (equal xy-add (q7525341-binary-value add y x))
        (equal (q7525341-binary-value add x zero) x)
        (equal (q7525341-binary-value add x neg-x) zero)
        (equal
         (q7525341-binary-value multiply xy-mul z)
         (q7525341-binary-value multiply x yz-mul))
        (equal xy-mul (q7525341-binary-value multiply y x))
        (equal (q7525341-binary-value multiply x one) x)
        (equal (q7525341-unary-value inverse zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q7525341-binary-value multiply x inv-x)
          one))
        (equal
         (q7525341-binary-value multiply x yz-add)
         (q7525341-binary-value
          add
          (q7525341-binary-value multiply x y)
          (q7525341-binary-value multiply x z))))))))

(defun-sk q7525341-ordered-field-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p carrier z))
     (and
      (not (q7525341-binary-relation-p less x x))
      (or
       (equal x y)
       (q7525341-binary-relation-p less x y)
       (q7525341-binary-relation-p less y x))
      (implies
       (and
        (q7525341-binary-relation-p less x y)
        (q7525341-binary-relation-p less y z))
       (q7525341-binary-relation-p less x z))
      (implies
       (q7525341-binary-relation-p less x y)
       (q7525341-binary-relation-p
        less
        (q7525341-binary-value add x z)
        (q7525341-binary-value add y z)))
      (implies
       (and
        (q7525341-binary-relation-p less zero x)
        (q7525341-binary-relation-p less zero y))
       (q7525341-binary-relation-p
        less zero
        (q7525341-binary-value multiply x y)))))))

(defun q7525341-scalar-leq (less left right)
  (not (q7525341-binary-relation-p less right left)))

(defun-sk q7525341-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p set x))
     (q7525341-scalar-leq less x bound))))

(defun-sk q7525341-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q7525341-member-p carrier bound)
     (q7525341-upper-bound-p carrier less set bound))))

(defun-sk q7525341-lower-bound-of-upper-bounds-p
    (carrier less set value)
  (forall (bound)
    (implies
     (and
      (q7525341-member-p carrier bound)
     (q7525341-upper-bound-p carrier less set bound))
     (q7525341-scalar-leq less value bound))))

(defun q7525341-least-upper-bound-p
    (carrier less set value)
  (and
   (q7525341-member-p carrier value)
   (q7525341-upper-bound-p carrier less set value)
   (q7525341-lower-bound-of-upper-bounds-p
    carrier less set value)))

(defun-sk q7525341-completeness-law-p
    (carrier less supremum)
  (forall (set)
    (implies
     (and
      (q7525341-valid-set-p carrier set)
      (q7525341-set-nonempty-p carrier set)
      (q7525341-bounded-above-p carrier less set))
     (q7525341-least-upper-bound-p
      carrier less set
      (q7525341-unary-value supremum set)))))

(defun q7525341-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q7525341-member-p carrier zero)
   (q7525341-member-p carrier one)
   (not (equal zero one))
   (q7525341-field-laws-p
    carrier zero one add multiply negate inverse)
   (q7525341-ordered-field-laws-p
    carrier zero add multiply less)
   (q7525341-binary-relation-p less zero one)
   (q7525341-completeness-law-p
    carrier less supremum)))

(defun-sk q7525341-order-interval-subset-p
    (carrier less set lower upper)
  (forall (y)
    (implies
     (and
      (q7525341-member-p carrier y)
      (q7525341-binary-relation-p less lower y)
      (q7525341-binary-relation-p less y upper))
     (q7525341-member-p set y))))

(defun-sk q7525341-order-open-radius-exists-p
    (carrier less set x)
  (exists (lower upper)
    (and
     (q7525341-member-p carrier lower)
     (q7525341-member-p carrier upper)
     (q7525341-binary-relation-p less lower x)
     (q7525341-binary-relation-p less x upper)
     (q7525341-order-interval-subset-p
      carrier less set lower upper))))

(defun-sk q7525341-order-open-at-every-point-p
    (carrier less set)
  (forall (x)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p set x))
     (q7525341-order-open-radius-exists-p
      carrier less set x))))

(defun-sk q7525341-order-open-characterization-p
    (carrier topology less)
  (forall (set)
    (implies
     (q7525341-valid-set-p carrier set)
     (iff
      (q7525341-open-set-p carrier topology set)
      (q7525341-order-open-at-every-point-p
       carrier less set)))))

(defun q7525341-real-order-topology-p
    (carrier topology less)
  (and
   (q7525341-topological-space-p carrier topology)
   (q7525341-order-open-characterization-p
    carrier topology less)))

;; Additive commutative groups and real modules.

(defun-sk q7525341-module-laws-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate scalar-action)
  (forall (a b x y z)
    (implies
     (and
      (q7525341-member-p scalar-carrier a)
      (q7525341-member-p scalar-carrier b)
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p carrier z))
     (let* ((xy (q7525341-binary-value add x y))
            (yz (q7525341-binary-value add y z))
            (neg-x (q7525341-unary-value negate x))
            (a-x (q7525341-binary-value scalar-action a x)))
       (and
        (q7525341-member-p carrier xy)
        (q7525341-member-p carrier neg-x)
        (q7525341-member-p carrier a-x)
        (equal
         (q7525341-binary-value add xy z)
         (q7525341-binary-value add x yz))
        (equal xy (q7525341-binary-value add y x))
        (equal (q7525341-binary-value add x zero) x)
        (equal (q7525341-binary-value add x neg-x) zero)
        (equal
         (q7525341-binary-value scalar-action scalar-one x)
         x)
        (equal
         (q7525341-binary-value
          scalar-action
          (q7525341-binary-value scalar-multiply a b)
          x)
         (q7525341-binary-value
          scalar-action a
          (q7525341-binary-value scalar-action b x)))
        (equal
         (q7525341-binary-value
          scalar-action
          (q7525341-binary-value scalar-add a b)
          x)
         (q7525341-binary-value
          add
          (q7525341-binary-value scalar-action a x)
          (q7525341-binary-value scalar-action b x)))
        (equal
         (q7525341-binary-value scalar-action a xy)
         (q7525341-binary-value
          add
          (q7525341-binary-value scalar-action a x)
          (q7525341-binary-value scalar-action a y)))
        (equal
         (q7525341-binary-value scalar-action scalar-zero x)
         zero))))))

(defun q7525341-module-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate scalar-action)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp negate)
   (tamep-functionp scalar-action)
   (q7525341-member-p carrier zero)
   (q7525341-module-laws-p
    scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
    carrier zero add negate scalar-action)))

;; Point-neighborhood formulations of continuity for addition, negation, and
;; scalar multiplication are equivalent to continuity in the product topology.

(defun-sk q7525341-add-neighborhood-maps-p
    (carrier add target left-open right-open)
  (forall (x y)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p left-open x)
      (q7525341-member-p right-open y))
     (q7525341-member-p
      target (q7525341-binary-value add x y)))))

(defun-sk q7525341-add-neighborhoods-exist-p
    (carrier topology add x y target)
  (exists (left-open right-open)
    (and
     (q7525341-open-set-p carrier topology left-open)
     (q7525341-open-set-p carrier topology right-open)
     (q7525341-member-p left-open x)
     (q7525341-member-p right-open y)
     (q7525341-add-neighborhood-maps-p
      carrier add target left-open right-open))))

(defun-sk q7525341-continuous-add-p
    (carrier topology add)
  (forall (x y target)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-open-set-p carrier topology target)
      (q7525341-member-p
       target (q7525341-binary-value add x y)))
     (q7525341-add-neighborhoods-exist-p
      carrier topology add x y target))))

(defun-sk q7525341-neg-neighborhood-maps-p
    (carrier negate target source)
  (forall (x)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p source x))
     (q7525341-member-p
      target (q7525341-unary-value negate x)))))

(defun-sk q7525341-neg-neighborhood-exists-p
    (carrier topology negate x target)
  (exists (source)
    (and
     (q7525341-open-set-p carrier topology source)
     (q7525341-member-p source x)
     (q7525341-neg-neighborhood-maps-p
      carrier negate target source))))

(defun-sk q7525341-continuous-neg-p
    (carrier topology negate)
  (forall (x target)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-open-set-p carrier topology target)
      (q7525341-member-p
       target (q7525341-unary-value negate x)))
     (q7525341-neg-neighborhood-exists-p
      carrier topology negate x target))))

(defun-sk q7525341-smul-neighborhood-maps-p
    (scalar-carrier carrier scalar-action target
     scalar-open vector-open)
  (forall (a x)
    (implies
     (and
      (q7525341-member-p scalar-carrier a)
      (q7525341-member-p carrier x)
      (q7525341-member-p scalar-open a)
      (q7525341-member-p vector-open x))
     (q7525341-member-p
      target
      (q7525341-binary-value scalar-action a x)))))

(defun-sk q7525341-smul-neighborhoods-exist-p
    (scalar-carrier scalar-topology carrier topology scalar-action
     a x target)
  (exists (scalar-open vector-open)
    (and
     (q7525341-open-set-p
      scalar-carrier scalar-topology scalar-open)
     (q7525341-open-set-p carrier topology vector-open)
     (q7525341-member-p scalar-open a)
     (q7525341-member-p vector-open x)
     (q7525341-smul-neighborhood-maps-p
      scalar-carrier carrier scalar-action target
      scalar-open vector-open))))

(defun-sk q7525341-continuous-smul-p
    (scalar-carrier scalar-topology carrier topology scalar-action)
  (forall (a x target)
    (implies
     (and
      (q7525341-member-p scalar-carrier a)
      (q7525341-member-p carrier x)
      (q7525341-open-set-p carrier topology target)
      (q7525341-member-p
       target
       (q7525341-binary-value scalar-action a x)))
     (q7525341-smul-neighborhoods-exist-p
      scalar-carrier scalar-topology carrier topology scalar-action
      a x target))))

(defun q7525341-real-topological-vector-space-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-topology carrier zero add negate scalar-action topology)
  (and
   (q7525341-module-p
    scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
    carrier zero add negate scalar-action)
   (q7525341-topological-space-p carrier topology)
   (q7525341-continuous-add-p carrier topology add)
   (q7525341-continuous-neg-p carrier topology negate)
   (q7525341-continuous-smul-p
    scalar-carrier scalar-topology
    carrier topology scalar-action)))

;; Convexity, semicontinuity on a set, and quasi-convex/concave sections.

(defun q7525341-scalar-nonnegative-p
    (scalar-carrier scalar-zero scalar-less value)
  (and
   (q7525341-member-p scalar-carrier value)
   (not
    (q7525341-binary-relation-p
     scalar-less value scalar-zero))))

(defun-sk q7525341-convex-set-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add scalar-action set)
  (forall (a b x y)
    (implies
     (and
      (q7525341-scalar-nonnegative-p
       scalar-carrier scalar-zero scalar-less a)
      (q7525341-scalar-nonnegative-p
       scalar-carrier scalar-zero scalar-less b)
      (equal
       (q7525341-binary-value scalar-add a b)
       scalar-one)
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p set x)
      (q7525341-member-p set y))
     (q7525341-member-p
      set
      (q7525341-binary-value
       vector-add
       (q7525341-binary-value scalar-action a x)
       (q7525341-binary-value scalar-action b y))))))

(defun-sk q7525341-lower-sublevel-closed-representation-p
    (carrier domain function fixed beta-carrier beta-le
     threshold closed)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (iff
      (and
       (q7525341-member-p domain x)
       (q7525341-binary-relation-p
        beta-le
        (q7525341-binary-value function x fixed)
        threshold))
      (and
       (q7525341-member-p domain x)
       (q7525341-member-p closed x))))))

(defun-sk q7525341-lower-sublevel-closed-exists-p
    (carrier topology domain function fixed
     beta-carrier beta-le threshold)
  (exists (closed)
    (and
     (q7525341-closed-set-p carrier topology closed)
     (q7525341-lower-sublevel-closed-representation-p
      carrier domain function fixed beta-carrier beta-le
      threshold closed))))

(defun-sk q7525341-lower-semicontinuous-section-p
    (carrier topology domain function fixed beta-carrier beta-le)
  (forall (threshold)
    (implies
     (q7525341-member-p beta-carrier threshold)
     (q7525341-lower-sublevel-closed-exists-p
      carrier topology domain function fixed
      beta-carrier beta-le threshold))))

(defun-sk q7525341-upper-superlevel-closed-representation-p
    (carrier domain function fixed beta-carrier beta-le
     threshold closed)
  (forall (y)
    (implies
     (q7525341-member-p carrier y)
     (iff
      (and
       (q7525341-member-p domain y)
       (q7525341-binary-relation-p
        beta-le threshold
        (q7525341-binary-value function fixed y)))
      (and
       (q7525341-member-p domain y)
       (q7525341-member-p closed y))))))

(defun-sk q7525341-upper-superlevel-closed-exists-p
    (carrier topology domain function fixed
     beta-carrier beta-le threshold)
  (exists (closed)
    (and
     (q7525341-closed-set-p carrier topology closed)
     (q7525341-upper-superlevel-closed-representation-p
      carrier domain function fixed beta-carrier beta-le
      threshold closed))))

(defun-sk q7525341-upper-semicontinuous-section-p
    (carrier topology domain function fixed beta-carrier beta-le)
  (forall (threshold)
    (implies
     (q7525341-member-p beta-carrier threshold)
     (q7525341-upper-superlevel-closed-exists-p
      carrier topology domain function fixed
      beta-carrier beta-le threshold))))

(defun-sk q7525341-all-lower-semicontinuous-p
    (e-carrier e-topology x-set f-carrier y-set
     function beta-carrier beta-le)
  (forall (y)
    (implies
     (and
      (q7525341-member-p f-carrier y)
      (q7525341-member-p y-set y))
     (q7525341-lower-semicontinuous-section-p
      e-carrier e-topology x-set function y
      beta-carrier beta-le))))

(defun-sk q7525341-all-upper-semicontinuous-p
    (e-carrier x-set f-carrier f-topology y-set
     function beta-carrier beta-le)
  (forall (x)
    (implies
     (and
      (q7525341-member-p e-carrier x)
      (q7525341-member-p x-set x))
     (q7525341-upper-semicontinuous-section-p
      f-carrier f-topology y-set function x
      beta-carrier beta-le))))

(defun-sk q7525341-quasiconvex-section-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add scalar-action domain function fixed
     beta-carrier beta-le)
  (forall (threshold a b x y)
    (implies
     (and
      (q7525341-member-p beta-carrier threshold)
      (q7525341-scalar-nonnegative-p
       scalar-carrier scalar-zero scalar-less a)
      (q7525341-scalar-nonnegative-p
       scalar-carrier scalar-zero scalar-less b)
      (equal
       (q7525341-binary-value scalar-add a b)
       scalar-one)
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p domain x)
      (q7525341-member-p domain y)
      (q7525341-binary-relation-p
       beta-le
       (q7525341-binary-value function x fixed)
       threshold)
      (q7525341-binary-relation-p
       beta-le
       (q7525341-binary-value function y fixed)
       threshold))
     (let ((combination
            (q7525341-binary-value
             vector-add
             (q7525341-binary-value scalar-action a x)
             (q7525341-binary-value scalar-action b y))))
       (and
        (q7525341-member-p domain combination)
        (q7525341-binary-relation-p
         beta-le
         (q7525341-binary-value function combination fixed)
         threshold))))))

(defun-sk q7525341-all-quasiconvex-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     e-carrier e-add e-smul x-set f-carrier y-set
     function beta-carrier beta-le)
  (forall (y)
    (implies
     (and
      (q7525341-member-p f-carrier y)
      (q7525341-member-p y-set y))
     (q7525341-quasiconvex-section-p
      scalar-carrier scalar-zero scalar-one scalar-add scalar-less
      e-carrier e-add e-smul x-set function y
      beta-carrier beta-le))))

(defun-sk q7525341-quasiconcave-section-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add scalar-action domain function fixed
     beta-carrier beta-le)
  (forall (threshold a b x y)
    (implies
     (and
      (q7525341-member-p beta-carrier threshold)
      (q7525341-scalar-nonnegative-p
       scalar-carrier scalar-zero scalar-less a)
      (q7525341-scalar-nonnegative-p
       scalar-carrier scalar-zero scalar-less b)
      (equal
       (q7525341-binary-value scalar-add a b)
       scalar-one)
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p domain x)
      (q7525341-member-p domain y)
      (q7525341-binary-relation-p
       beta-le threshold
       (q7525341-binary-value function fixed x))
      (q7525341-binary-relation-p
       beta-le threshold
       (q7525341-binary-value function fixed y)))
     (let ((combination
            (q7525341-binary-value
             vector-add
             (q7525341-binary-value scalar-action a x)
             (q7525341-binary-value scalar-action b y))))
       (and
        (q7525341-member-p domain combination)
        (q7525341-binary-relation-p
         beta-le threshold
         (q7525341-binary-value function fixed combination)))))))

(defun-sk q7525341-all-quasiconcave-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     e-carrier x-set f-carrier f-add f-smul y-set
     function beta-carrier beta-le)
  (forall (x)
    (implies
     (and
      (q7525341-member-p e-carrier x)
      (q7525341-member-p x-set x))
     (q7525341-quasiconcave-section-p
      scalar-carrier scalar-zero scalar-one scalar-add scalar-less
      f-carrier f-add f-smul y-set function x
      beta-carrier beta-le))))

;; Dense linear order and the four exact IsLUB/IsGLB conditions.

(defun-sk q7525341-linear-order-laws-p (carrier le)
  (forall (x y z)
    (implies
     (and
      (q7525341-member-p carrier x)
      (q7525341-member-p carrier y)
      (q7525341-member-p carrier z))
     (and
      (q7525341-binary-relation-p le x x)
      (implies
       (and
        (q7525341-binary-relation-p le x y)
        (q7525341-binary-relation-p le y x))
       (equal x y))
      (implies
       (and
        (q7525341-binary-relation-p le x y)
        (q7525341-binary-relation-p le y z))
       (q7525341-binary-relation-p le x z))
      (or
       (q7525341-binary-relation-p le x y)
       (q7525341-binary-relation-p le y x))))))

(defun q7525341-beta-less-p (le left right)
  (and
   (q7525341-binary-relation-p le left right)
   (not (equal left right))))

(defun-sk q7525341-between-exists-p
    (carrier le left right)
  (exists (middle)
    (and
     (q7525341-member-p carrier middle)
     (q7525341-beta-less-p le left middle)
     (q7525341-beta-less-p le middle right))))

(defun-sk q7525341-dense-order-law-p (carrier le)
  (forall (left right)
    (implies
     (and
      (q7525341-member-p carrier left)
      (q7525341-member-p carrier right)
      (q7525341-beta-less-p le left right))
     (q7525341-between-exists-p carrier le left right))))

(defun q7525341-dense-linear-order-p (carrier le)
  (and
   (tamep-functionp carrier)
   (tamep-functionp le)
   (q7525341-linear-order-laws-p carrier le)
   (q7525341-dense-order-law-p carrier le)))

(defun-sk q7525341-function-typed-p
    (e-carrier f-carrier beta-carrier function)
  (forall (x y)
    (implies
     (and
      (q7525341-member-p e-carrier x)
      (q7525341-member-p f-carrier y))
     (q7525341-member-p
      beta-carrier
      (q7525341-binary-value function x y)))))

(defun-sk q7525341-unary-function-typed-p
    (carrier beta-carrier function)
  (forall (x)
    (implies
     (q7525341-member-p carrier x)
     (q7525341-member-p
      beta-carrier
      (q7525341-unary-value function x)))))

(defun-sk q7525341-row-upper-bound-p
    (f-carrier y-set function x beta-le bound)
  (forall (y)
    (implies
     (and
      (q7525341-member-p f-carrier y)
      (q7525341-member-p y-set y))
     (q7525341-binary-relation-p
      beta-le
      (q7525341-binary-value function x y)
      bound))))

(defun-sk q7525341-row-lub-least-p
    (f-carrier y-set function x beta-carrier beta-le value)
  (forall (bound)
    (implies
     (and
      (q7525341-member-p beta-carrier bound)
      (q7525341-row-upper-bound-p
       f-carrier y-set function x beta-le bound))
     (q7525341-binary-relation-p beta-le value bound))))

(defun q7525341-row-is-lub-p
    (f-carrier y-set function x beta-carrier beta-le value)
  (and
   (q7525341-member-p beta-carrier value)
   (q7525341-row-upper-bound-p
    f-carrier y-set function x beta-le value)
   (q7525341-row-lub-least-p
    f-carrier y-set function x beta-carrier beta-le value)))

(defun-sk q7525341-all-row-lubs-p
    (e-carrier x-set f-carrier y-set function
     beta-carrier beta-le sup-y)
  (forall (x)
    (implies
     (and
      (q7525341-member-p e-carrier x)
      (q7525341-member-p x-set x))
     (q7525341-row-is-lub-p
      f-carrier y-set function x beta-carrier beta-le
      (q7525341-unary-value sup-y x)))))

(defun-sk q7525341-sup-y-lower-bound-p
    (e-carrier x-set sup-y beta-le bound)
  (forall (x)
    (implies
     (and
      (q7525341-member-p e-carrier x)
      (q7525341-member-p x-set x))
     (q7525341-binary-relation-p
      beta-le bound
      (q7525341-unary-value sup-y x)))))

(defun-sk q7525341-sup-y-glb-greatest-p
    (e-carrier x-set sup-y beta-carrier beta-le value)
  (forall (bound)
    (implies
     (and
      (q7525341-member-p beta-carrier bound)
      (q7525341-sup-y-lower-bound-p
       e-carrier x-set sup-y beta-le bound))
     (q7525341-binary-relation-p beta-le bound value))))

(defun q7525341-sup-y-is-glb-p
    (e-carrier x-set sup-y beta-carrier beta-le value)
  (and
   (q7525341-member-p beta-carrier value)
   (q7525341-sup-y-lower-bound-p
    e-carrier x-set sup-y beta-le value)
   (q7525341-sup-y-glb-greatest-p
    e-carrier x-set sup-y beta-carrier beta-le value)))

(defun-sk q7525341-column-lower-bound-p
    (e-carrier x-set function y beta-le bound)
  (forall (x)
    (implies
     (and
      (q7525341-member-p e-carrier x)
      (q7525341-member-p x-set x))
     (q7525341-binary-relation-p
      beta-le bound
      (q7525341-binary-value function x y)))))

(defun-sk q7525341-column-glb-greatest-p
    (e-carrier x-set function y beta-carrier beta-le value)
  (forall (bound)
    (implies
     (and
      (q7525341-member-p beta-carrier bound)
      (q7525341-column-lower-bound-p
       e-carrier x-set function y beta-le bound))
     (q7525341-binary-relation-p beta-le bound value))))

(defun q7525341-column-is-glb-p
    (e-carrier x-set function y beta-carrier beta-le value)
  (and
   (q7525341-member-p beta-carrier value)
   (q7525341-column-lower-bound-p
    e-carrier x-set function y beta-le value)
   (q7525341-column-glb-greatest-p
    e-carrier x-set function y beta-carrier beta-le value)))

(defun-sk q7525341-all-column-glbs-p
    (e-carrier x-set f-carrier y-set function
     beta-carrier beta-le inf-x)
  (forall (y)
    (implies
     (and
      (q7525341-member-p f-carrier y)
      (q7525341-member-p y-set y))
     (q7525341-column-is-glb-p
      e-carrier x-set function y beta-carrier beta-le
      (q7525341-unary-value inf-x y)))))

(defun-sk q7525341-inf-x-upper-bound-p
    (f-carrier y-set inf-x beta-le bound)
  (forall (y)
    (implies
     (and
      (q7525341-member-p f-carrier y)
      (q7525341-member-p y-set y))
     (q7525341-binary-relation-p
      beta-le
      (q7525341-unary-value inf-x y)
      bound))))

(defun-sk q7525341-inf-x-lub-least-p
    (f-carrier y-set inf-x beta-carrier beta-le value)
  (forall (bound)
    (implies
     (and
      (q7525341-member-p beta-carrier bound)
      (q7525341-inf-x-upper-bound-p
       f-carrier y-set inf-x beta-le bound))
     (q7525341-binary-relation-p beta-le value bound))))

(defun q7525341-inf-x-is-lub-p
    (f-carrier y-set inf-x beta-carrier beta-le value)
  (and
   (q7525341-member-p beta-carrier value)
   (q7525341-inf-x-upper-bound-p
    f-carrier y-set inf-x beta-le value)
   (q7525341-inf-x-lub-least-p
    f-carrier y-set inf-x beta-carrier beta-le value)))

(defun thousand-theorems-q7525341-sion-s-minimax-theorem-statement
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-inverse scalar-less scalar-supremum
     scalar-topology
     e-carrier e-zero e-add e-negate e-smul e-topology x-set
     f-carrier f-zero f-add f-negate f-smul f-topology y-set
     beta-carrier beta-le function sup-y inf-sup inf-x sup-inf)
  (implies
   (and
    (q7525341-real-field-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-inverse scalar-less scalar-supremum)
    (q7525341-real-order-topology-p
     scalar-carrier scalar-topology scalar-less)
    (q7525341-real-topological-vector-space-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-topology
     e-carrier e-zero e-add e-negate e-smul e-topology)
    (q7525341-real-topological-vector-space-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-topology
     f-carrier f-zero f-add f-negate f-smul f-topology)
    (q7525341-dense-linear-order-p beta-carrier beta-le)
    (q7525341-valid-set-p e-carrier x-set)
    (q7525341-valid-set-p f-carrier y-set)
    (q7525341-set-nonempty-p e-carrier x-set)
    (q7525341-compact-set-p e-carrier e-topology x-set)
    (q7525341-convex-set-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     f-carrier f-add f-smul y-set)
    (tamep-functionp function)
    (tamep-functionp sup-y)
    (tamep-functionp inf-x)
    (q7525341-function-typed-p
     e-carrier f-carrier beta-carrier function)
    (q7525341-unary-function-typed-p
     e-carrier beta-carrier sup-y)
    (q7525341-unary-function-typed-p
     f-carrier beta-carrier inf-x)
    (q7525341-all-lower-semicontinuous-p
     e-carrier e-topology x-set f-carrier y-set
     function beta-carrier beta-le)
    (q7525341-all-quasiconvex-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     e-carrier e-add e-smul x-set f-carrier y-set
     function beta-carrier beta-le)
    (q7525341-all-upper-semicontinuous-p
     e-carrier x-set f-carrier f-topology y-set
     function beta-carrier beta-le)
    (q7525341-all-quasiconcave-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     e-carrier x-set f-carrier f-add f-smul y-set
     function beta-carrier beta-le)
    (q7525341-all-row-lubs-p
     e-carrier x-set f-carrier y-set function
     beta-carrier beta-le sup-y)
    (q7525341-sup-y-is-glb-p
     e-carrier x-set sup-y beta-carrier beta-le inf-sup)
    (q7525341-all-column-glbs-p
     e-carrier x-set f-carrier y-set function
     beta-carrier beta-le inf-x)
    (q7525341-inf-x-is-lub-p
     f-carrier y-set inf-x beta-carrier beta-le sup-inf))
   (equal inf-sup sup-inf)))

(value-triple :itpeval-statement-checked)
:q
