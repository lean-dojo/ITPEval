;; Statement-only formalization of thousand-theorems corpus artifact Q303402,
;; "Rank–nullity theorem": for an arbitrary linear map between arbitrary
;; modules over a ring satisfying HasRankNullity, the cardinal rank of the
;; range plus the cardinal rank of the kernel is the rank of the domain.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent arbitrary rings, modules, linear
;; maps, submodules, and rank-cardinal representatives.  Carrier predicates
;; and maps are unbounded; no module, set, function, or cardinal is encoded by
;; a finite table.

(defstub q303402-ring-member-p (ring value) t)
(defstub q303402-ring-zero (ring) t)
(defstub q303402-ring-one (ring) t)
(defstub q303402-ring-add (ring left right) t)
(defstub q303402-ring-multiply (ring left right) t)
(defstub q303402-ring-negate (ring value) t)

(defstub q303402-module-member-p (ring module value) t)
(defstub q303402-module-zero (ring module) t)
(defstub q303402-module-add (ring module left right) t)
(defstub q303402-module-negate (ring module value) t)
(defstub q303402-module-smul (ring module scalar value) t)

(defstub q303402-linear-map-apply
  (ring domain codomain linear-map value)
  t)

(defstub q303402-generic-submodule-member-p
  (ring module submodule value)
  t)

;; Each rank is represented by an arbitrary unary carrier.  Equality and
;; addition of these cardinal representatives are defined below by
;; equipotence and tagged disjoint union, so infinite ranks remain available.

(defstub q303402-module-rank-carrier (ring module) t)
(defstub q303402-submodule-rank-carrier (ring module submodule) t)
(defstub q303402-quotient-rank-carrier (ring module submodule) t)

;; Ring, module, and linear-map structure.

(defun-sk q303402-ring-laws-p (ring)
  (forall (x y z)
    (and
     (implies
      (and
       (q303402-ring-member-p ring x)
       (q303402-ring-member-p ring y))
      (and
       (q303402-ring-member-p
        ring (q303402-ring-add ring x y))
       (q303402-ring-member-p
        ring (q303402-ring-multiply ring x y))
       (equal
        (q303402-ring-add ring x y)
        (q303402-ring-add ring y x))))
     (implies
      (q303402-ring-member-p ring x)
      (and
       (q303402-ring-member-p
        ring (q303402-ring-negate ring x))
       (equal
        (q303402-ring-add ring x (q303402-ring-zero ring))
        x)
       (equal
        (q303402-ring-add
         ring x (q303402-ring-negate ring x))
        (q303402-ring-zero ring))
       (equal
        (q303402-ring-multiply ring x (q303402-ring-one ring))
        x)
       (equal
        (q303402-ring-multiply ring (q303402-ring-one ring) x)
        x)))
     (implies
      (and
       (q303402-ring-member-p ring x)
       (q303402-ring-member-p ring y)
       (q303402-ring-member-p ring z))
      (and
       (equal
        (q303402-ring-add
         ring (q303402-ring-add ring x y) z)
        (q303402-ring-add
         ring x (q303402-ring-add ring y z)))
       (equal
        (q303402-ring-multiply
         ring (q303402-ring-multiply ring x y) z)
        (q303402-ring-multiply
         ring x (q303402-ring-multiply ring y z)))
       (equal
        (q303402-ring-multiply
         ring x (q303402-ring-add ring y z))
        (q303402-ring-add
         ring
         (q303402-ring-multiply ring x y)
         (q303402-ring-multiply ring x z)))
       (equal
        (q303402-ring-multiply
         ring (q303402-ring-add ring x y) z)
        (q303402-ring-add
         ring
         (q303402-ring-multiply ring x z)
         (q303402-ring-multiply ring y z))))))))

(defun q303402-ring-p (ring)
  (and
   (q303402-ring-member-p ring (q303402-ring-zero ring))
   (q303402-ring-member-p ring (q303402-ring-one ring))
   (q303402-ring-laws-p ring)))

(defun-sk q303402-module-laws-p (ring module)
  (forall (a b u v w)
    (and
     (implies
      (and
       (q303402-module-member-p ring module u)
       (q303402-module-member-p ring module v))
      (and
       (q303402-module-member-p
        ring module (q303402-module-add ring module u v))
       (equal
        (q303402-module-add ring module u v)
        (q303402-module-add ring module v u))))
     (implies
      (q303402-module-member-p ring module u)
      (and
       (q303402-module-member-p
        ring module (q303402-module-negate ring module u))
       (equal
        (q303402-module-add
         ring module u (q303402-module-zero ring module))
        u)
       (equal
        (q303402-module-add
         ring module u (q303402-module-negate ring module u))
        (q303402-module-zero ring module))
       (equal
        (q303402-module-smul
         ring module (q303402-ring-one ring) u)
        u)
       (equal
        (q303402-module-smul
         ring module (q303402-ring-zero ring) u)
        (q303402-module-zero ring module))))
     (implies
      (and
       (q303402-module-member-p ring module u)
       (q303402-module-member-p ring module v)
       (q303402-module-member-p ring module w))
      (equal
       (q303402-module-add
        ring module (q303402-module-add ring module u v) w)
       (q303402-module-add
        ring module u (q303402-module-add ring module v w))))
     (implies
      (and
       (q303402-ring-member-p ring a)
       (q303402-module-member-p ring module u))
      (q303402-module-member-p
       ring module (q303402-module-smul ring module a u)))
     (implies
      (q303402-ring-member-p ring a)
      (equal
       (q303402-module-smul
        ring module a (q303402-module-zero ring module))
       (q303402-module-zero ring module)))
     (implies
      (and
       (q303402-ring-member-p ring a)
       (q303402-module-member-p ring module u)
       (q303402-module-member-p ring module v))
      (equal
       (q303402-module-smul
        ring module a (q303402-module-add ring module u v))
       (q303402-module-add
        ring module
        (q303402-module-smul ring module a u)
        (q303402-module-smul ring module a v))))
     (implies
      (and
       (q303402-ring-member-p ring a)
       (q303402-ring-member-p ring b)
       (q303402-module-member-p ring module u))
      (and
       (equal
        (q303402-module-smul
         ring module (q303402-ring-add ring a b) u)
        (q303402-module-add
         ring module
         (q303402-module-smul ring module a u)
         (q303402-module-smul ring module b u)))
       (equal
        (q303402-module-smul
         ring module (q303402-ring-multiply ring a b) u)
        (q303402-module-smul
         ring module a
         (q303402-module-smul ring module b u))))))))

(defun q303402-module-p (ring module)
  (and
   (q303402-ring-p ring)
   (q303402-module-member-p
    ring module (q303402-module-zero ring module))
   (q303402-module-laws-p ring module)))

(defun-sk q303402-linear-map-laws-p
    (ring domain codomain linear-map)
  (forall (a u v)
    (and
     (implies
      (q303402-module-member-p ring domain u)
      (q303402-module-member-p
       ring codomain
       (q303402-linear-map-apply
        ring domain codomain linear-map u)))
     (implies
      (and
       (q303402-module-member-p ring domain u)
       (q303402-module-member-p ring domain v))
      (equal
       (q303402-linear-map-apply
        ring domain codomain linear-map
        (q303402-module-add ring domain u v))
       (q303402-module-add
        ring codomain
        (q303402-linear-map-apply
         ring domain codomain linear-map u)
        (q303402-linear-map-apply
         ring domain codomain linear-map v))))
     (implies
      (and
       (q303402-ring-member-p ring a)
       (q303402-module-member-p ring domain u))
      (equal
       (q303402-linear-map-apply
        ring domain codomain linear-map
        (q303402-module-smul ring domain a u))
       (q303402-module-smul
        ring codomain a
        (q303402-linear-map-apply
         ring domain codomain linear-map u)))))))

(defun q303402-linear-map-p
    (ring domain codomain linear-map)
  (and
   (q303402-module-p ring domain)
   (q303402-module-p ring codomain)
   (q303402-linear-map-laws-p
    ring domain codomain linear-map)))

;; Kernel and range are distinguished submodule tags whose membership is
;; defined directly from the map, while all other submodule tags retain the
;; conservative generic membership interface.

(defun q303402-kernel-tag
    (ring domain codomain linear-map)
  (list :q303402-kernel ring domain codomain linear-map))

(defun q303402-range-tag
    (ring domain codomain linear-map)
  (list :q303402-range ring domain codomain linear-map))

(defun q303402-kernel-tag-p (submodule)
  (and
   (true-listp submodule)
   (equal (len submodule) 5)
   (equal (car submodule) :q303402-kernel)))

(defun q303402-range-tag-p (submodule)
  (and
   (true-listp submodule)
   (equal (len submodule) 5)
   (equal (car submodule) :q303402-range)))

(defun q303402-kernel-member-p
    (ring domain codomain linear-map value)
  (and
   (q303402-module-member-p ring domain value)
   (equal
    (q303402-linear-map-apply
     ring domain codomain linear-map value)
    (q303402-module-zero ring codomain))))

(defun-sk q303402-range-member-p
    (ring domain codomain linear-map value)
  (exists (preimage)
    (and
     (q303402-module-member-p ring codomain value)
     (q303402-module-member-p ring domain preimage)
     (equal
      (q303402-linear-map-apply
       ring domain codomain linear-map preimage)
      value))))

(defun q303402-submodule-member-p
    (ring module submodule value)
  (cond
   ((and
     (q303402-kernel-tag-p submodule)
     (equal ring (nth 1 submodule))
     (equal module (nth 2 submodule)))
    (q303402-kernel-member-p
     ring
     (nth 2 submodule)
     (nth 3 submodule)
     (nth 4 submodule)
     value))
   ((and
     (q303402-range-tag-p submodule)
     (equal ring (nth 1 submodule))
     (equal module (nth 3 submodule)))
    (q303402-range-member-p
     ring
     (nth 2 submodule)
     (nth 3 submodule)
     (nth 4 submodule)
     value))
   (t
    (q303402-generic-submodule-member-p
     ring module submodule value))))

(defun-sk q303402-submodule-laws-p (ring module submodule)
  (forall (a u v)
    (and
     (implies
      (q303402-submodule-member-p ring module submodule u)
      (and
       (q303402-module-member-p ring module u)
       (q303402-submodule-member-p
        ring module submodule
        (q303402-module-negate ring module u))))
     (implies
      (and
       (q303402-submodule-member-p ring module submodule u)
       (q303402-submodule-member-p ring module submodule v))
      (q303402-submodule-member-p
       ring module submodule
       (q303402-module-add ring module u v)))
     (implies
      (and
       (q303402-ring-member-p ring a)
       (q303402-submodule-member-p ring module submodule u))
      (q303402-submodule-member-p
       ring module submodule
       (q303402-module-smul ring module a u))))))

(defun q303402-submodule-p (ring module submodule)
  (and
   (q303402-module-p ring module)
   (q303402-submodule-member-p
    ring module submodule (q303402-module-zero ring module))
   (q303402-submodule-laws-p ring module submodule)))

;; Cardinal representatives and cardinal arithmetic.

(defun q303402-cardinal-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun q303402-cardinal-carrier-p (carrier)
  (tamep-functionp carrier))

(defun q303402-map-value (mapping value)
  (apply$ mapping (list value)))

(defun-sk q303402-map-total-p (source target mapping)
  (forall (value)
    (implies
     (q303402-cardinal-member-p source value)
     (q303402-cardinal-member-p
      target (q303402-map-value mapping value)))))

(defun-sk q303402-map-injective-p (source mapping)
  (forall (left right)
    (implies
     (and
      (q303402-cardinal-member-p source left)
      (q303402-cardinal-member-p source right)
      (equal
       (q303402-map-value mapping left)
       (q303402-map-value mapping right)))
     (equal left right))))

(defun-sk q303402-map-preimage-exists-p
    (source mapping target-value)
  (exists (source-value)
    (and
     (q303402-cardinal-member-p source source-value)
     (equal
      (q303402-map-value mapping source-value)
      target-value))))

(defun-sk q303402-map-surjective-p (source target mapping)
  (forall (target-value)
    (implies
     (q303402-cardinal-member-p target target-value)
     (q303402-map-preimage-exists-p
      source mapping target-value))))

(defun q303402-injection-p (source target mapping)
  (and
   (q303402-cardinal-carrier-p source)
   (q303402-cardinal-carrier-p target)
   (tamep-functionp mapping)
   (q303402-map-total-p source target mapping)
   (q303402-map-injective-p source mapping)))

(defun q303402-bijection-p (source target mapping)
  (and
   (q303402-injection-p source target mapping)
   (q303402-map-surjective-p source target mapping)))

(defun-sk q303402-cardinal-leq-p (left right)
  (exists (mapping)
    (q303402-injection-p left right mapping)))

(defun-sk q303402-cardinal-equal-p (left right)
  (exists (mapping)
    (q303402-bijection-p left right mapping)))

(defun q303402-left-summand (value)
  (list :q303402-left value))

(defun q303402-right-summand (value)
  (list :q303402-right value))

(defun q303402-sum-member-p (left right value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (or
    (and
     (equal (car value) :q303402-left)
     (q303402-cardinal-member-p left (cadr value)))
    (and
     (equal (car value) :q303402-right)
     (q303402-cardinal-member-p right (cadr value))))))

(defun-sk q303402-sum-map-total-p
    (left right target mapping)
  (forall (value)
    (implies
     (q303402-sum-member-p left right value)
     (q303402-cardinal-member-p
      target (q303402-map-value mapping value)))))

(defun-sk q303402-sum-map-injective-p
    (left right mapping)
  (forall (first second)
    (implies
     (and
      (q303402-sum-member-p left right first)
      (q303402-sum-member-p left right second)
      (equal
       (q303402-map-value mapping first)
       (q303402-map-value mapping second)))
     (equal first second))))

(defun-sk q303402-sum-map-preimage-exists-p
    (left right mapping target-value)
  (exists (source-value)
    (and
     (q303402-sum-member-p left right source-value)
     (equal
      (q303402-map-value mapping source-value)
      target-value))))

(defun-sk q303402-sum-map-surjective-p
    (left right target mapping)
  (forall (target-value)
    (implies
     (q303402-cardinal-member-p target target-value)
     (q303402-sum-map-preimage-exists-p
      left right mapping target-value))))

(defun-sk q303402-cardinal-sum-equal-p (left right target)
  (exists (mapping)
    (and
     (q303402-cardinal-carrier-p left)
     (q303402-cardinal-carrier-p right)
     (q303402-cardinal-carrier-p target)
     (tamep-functionp mapping)
     (q303402-sum-map-total-p left right target mapping)
     (q303402-sum-map-injective-p left right mapping)
     (q303402-sum-map-surjective-p
      left right target mapping))))

;; Finite-support linear combinations are association lists from arbitrary
;; indices to scalars.  This keeps linear independence unbounded in the index
;; carrier while retaining the source's finite-support quantification.

(defun q303402-coefficient-list-p
    (ring index-carrier coefficients)
  (if (consp coefficients)
      (and
       (consp (car coefficients))
       (q303402-cardinal-member-p
        index-carrier (caar coefficients))
       (q303402-ring-member-p ring (cdar coefficients))
       (not
        (assoc-equal
         (caar coefficients) (cdr coefficients)))
       (q303402-coefficient-list-p
        ring index-carrier (cdr coefficients)))
    (equal coefficients nil)))

(defun q303402-linear-combination
    (ring module family coefficients)
  (if (consp coefficients)
      (q303402-module-add
       ring module
       (q303402-module-smul
        ring module
        (cdar coefficients)
        (q303402-map-value family (caar coefficients)))
       (q303402-linear-combination
        ring module family (cdr coefficients)))
    (q303402-module-zero ring module)))

(defun q303402-subset-linear-combination
    (ring module coefficients)
  (if (consp coefficients)
      (q303402-module-add
       ring module
       (q303402-module-smul
        ring module (cdar coefficients) (caar coefficients))
       (q303402-subset-linear-combination
        ring module (cdr coefficients)))
    (q303402-module-zero ring module)))

(defun q303402-all-coefficients-zero-p (ring coefficients)
  (if (consp coefficients)
      (and
       (equal (cdar coefficients) (q303402-ring-zero ring))
       (q303402-all-coefficients-zero-p
        ring (cdr coefficients)))
    (equal coefficients nil)))

(defun-sk q303402-family-total-to-module-p
    (ring module index-carrier family)
  (forall (index)
    (implies
     (q303402-cardinal-member-p index-carrier index)
     (q303402-module-member-p
      ring module (q303402-map-value family index)))))

(defun-sk q303402-family-total-to-submodule-p
    (ring module submodule index-carrier family)
  (forall (index)
    (implies
     (q303402-cardinal-member-p index-carrier index)
     (q303402-submodule-member-p
      ring module submodule
      (q303402-map-value family index)))))

(defun-sk q303402-linear-independent-laws-p
    (ring module index-carrier family)
  (forall (coefficients)
    (implies
     (and
      (q303402-coefficient-list-p
       ring index-carrier coefficients)
      (equal
       (q303402-linear-combination
        ring module family coefficients)
       (q303402-module-zero ring module)))
     (q303402-all-coefficients-zero-p ring coefficients))))

(defun-sk q303402-quotient-linear-independent-laws-p
    (ring module submodule index-carrier family)
  (forall (coefficients)
    (implies
     (and
      (q303402-coefficient-list-p
       ring index-carrier coefficients)
      (q303402-submodule-member-p
       ring module submodule
       (q303402-linear-combination
        ring module family coefficients)))
     (q303402-all-coefficients-zero-p ring coefficients))))

(defun q303402-linear-independent-family-p
    (ring module index-carrier family)
  (and
   (q303402-cardinal-carrier-p index-carrier)
   (tamep-functionp family)
   (q303402-family-total-to-module-p
    ring module index-carrier family)
   (q303402-linear-independent-laws-p
    ring module index-carrier family)))

(defun q303402-submodule-linear-independent-family-p
    (ring module submodule index-carrier family)
  (and
   (q303402-cardinal-carrier-p index-carrier)
   (tamep-functionp family)
   (q303402-family-total-to-submodule-p
    ring module submodule index-carrier family)
   (q303402-linear-independent-laws-p
    ring module index-carrier family)))

(defun q303402-quotient-linear-independent-family-p
    (ring module submodule index-carrier family)
  (and
   (q303402-cardinal-carrier-p index-carrier)
   (tamep-functionp family)
   (q303402-family-total-to-module-p
    ring module index-carrier family)
   (q303402-quotient-linear-independent-laws-p
    ring module submodule index-carrier family)))

(defun-sk q303402-subset-of-module-p (ring module subset)
  (forall (value)
    (implies
     (q303402-cardinal-member-p subset value)
     (q303402-module-member-p ring module value))))

(defun-sk q303402-linear-independent-subset-laws-p
    (ring module subset)
  (forall (coefficients)
    (implies
     (and
      (q303402-coefficient-list-p ring subset coefficients)
      (equal
       (q303402-subset-linear-combination
        ring module coefficients)
       (q303402-module-zero ring module)))
     (q303402-all-coefficients-zero-p ring coefficients))))

(defun q303402-linear-independent-subset-p
    (ring module subset)
  (and
   (q303402-cardinal-carrier-p subset)
   (q303402-subset-of-module-p ring module subset)
   (q303402-linear-independent-subset-laws-p
    ring module subset)))

;; Module.rank is characterized as the least cardinal upper bound of all
;; linearly independent families.  Submodule rank uses inherited operations;
;; quotient rank uses independence modulo the submodule, which is exactly
;; linear independence in the quotient module.

(defun-sk q303402-module-rank-upper-bound-p
    (ring module bound)
  (forall (index-carrier family)
    (implies
     (q303402-linear-independent-family-p
      ring module index-carrier family)
     (q303402-cardinal-leq-p index-carrier bound))))

(defun-sk q303402-module-rank-least-p
    (ring module rank)
  (forall (bound)
    (implies
     (and
      (q303402-cardinal-carrier-p bound)
      (q303402-module-rank-upper-bound-p
       ring module bound))
     (q303402-cardinal-leq-p rank bound))))

(defun q303402-module-rank-spec-p (ring module)
  (let ((rank (q303402-module-rank-carrier ring module)))
    (and
     (q303402-cardinal-carrier-p rank)
     (q303402-module-rank-upper-bound-p ring module rank)
     (q303402-module-rank-least-p ring module rank))))

(defun-sk q303402-submodule-rank-upper-bound-p
    (ring module submodule bound)
  (forall (index-carrier family)
    (implies
     (q303402-submodule-linear-independent-family-p
      ring module submodule index-carrier family)
     (q303402-cardinal-leq-p index-carrier bound))))

(defun-sk q303402-submodule-rank-least-p
    (ring module submodule rank)
  (forall (bound)
    (implies
     (and
      (q303402-cardinal-carrier-p bound)
      (q303402-submodule-rank-upper-bound-p
       ring module submodule bound))
     (q303402-cardinal-leq-p rank bound))))

(defun q303402-submodule-rank-spec-p
    (ring module submodule)
  (let
      ((rank
        (q303402-submodule-rank-carrier
         ring module submodule)))
    (and
     (q303402-cardinal-carrier-p rank)
     (q303402-submodule-rank-upper-bound-p
      ring module submodule rank)
     (q303402-submodule-rank-least-p
      ring module submodule rank))))

(defun-sk q303402-quotient-rank-upper-bound-p
    (ring module submodule bound)
  (forall (index-carrier family)
    (implies
     (q303402-quotient-linear-independent-family-p
      ring module submodule index-carrier family)
     (q303402-cardinal-leq-p index-carrier bound))))

(defun-sk q303402-quotient-rank-least-p
    (ring module submodule rank)
  (forall (bound)
    (implies
     (and
      (q303402-cardinal-carrier-p bound)
      (q303402-quotient-rank-upper-bound-p
       ring module submodule bound))
     (q303402-cardinal-leq-p rank bound))))

(defun q303402-quotient-rank-spec-p
    (ring module submodule)
  (let
      ((rank
        (q303402-quotient-rank-carrier
         ring module submodule)))
    (and
     (q303402-cardinal-carrier-p rank)
     (q303402-quotient-rank-upper-bound-p
      ring module submodule rank)
     (q303402-quotient-rank-least-p
      ring module submodule rank))))

(defun-sk q303402-rank-semantics-p (ring)
  (forall (module submodule)
    (and
     (implies
      (q303402-module-p ring module)
      (q303402-module-rank-spec-p ring module))
     (implies
      (q303402-submodule-p ring module submodule)
      (and
       (q303402-submodule-rank-spec-p
        ring module submodule)
       (q303402-quotient-rank-spec-p
        ring module submodule))))))

;; This is the complete HasRankNullity package from the Lean source.  Its
;; first field says every module has an independent subset equipotent to its
;; rank; its second field gives quotient-rank plus submodule-rank equals
;; module-rank for every module and every submodule.

(defun-sk q303402-rank-attained-p (ring module)
  (exists (subset)
    (and
     (q303402-linear-independent-subset-p
      ring module subset)
     (q303402-cardinal-equal-p
      subset (q303402-module-rank-carrier ring module)))))

(defun-sk q303402-all-module-ranks-attained-p (ring)
  (forall (module)
    (implies
     (q303402-module-p ring module)
     (q303402-rank-attained-p ring module))))

(defun-sk q303402-rank-quotient-add-rank-p (ring)
  (forall (module submodule)
    (implies
     (q303402-submodule-p ring module submodule)
     (q303402-cardinal-sum-equal-p
      (q303402-quotient-rank-carrier
       ring module submodule)
      (q303402-submodule-rank-carrier
       ring module submodule)
      (q303402-module-rank-carrier ring module)))))

(defun q303402-has-rank-nullity-p (ring)
  (and
   (q303402-all-module-ranks-attained-p ring)
   (q303402-rank-quotient-add-rank-p ring)))

(defun-sk thousand-theorems-q303402-rank-nullity-statement ()
  (forall (ring domain codomain linear-map)
    (implies
     (and
      (q303402-linear-map-p
       ring domain codomain linear-map)
      (q303402-rank-semantics-p ring)
      (q303402-has-rank-nullity-p ring))
     (q303402-cardinal-sum-equal-p
      (q303402-submodule-rank-carrier
       ring
       codomain
       (q303402-range-tag
        ring domain codomain linear-map))
      (q303402-submodule-rank-carrier
       ring
       domain
       (q303402-kernel-tag
        ring domain codomain linear-map))
      (q303402-module-rank-carrier ring domain)))))

(value-triple :itpeval-statement-checked)
:q
