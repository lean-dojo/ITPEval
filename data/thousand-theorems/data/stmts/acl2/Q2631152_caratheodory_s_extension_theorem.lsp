;; Statement-only formalization of thousand-theorems corpus artifact Q2631152,
;; "Carathéodory's extension theorem": the measure constructed from a
;; sigma-subadditive additive content on a semiring of sets agrees with that
;; content on every set of the semiring. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Arbitrary function, predicate, set, and family objects are represented by
;; tags interpreted through conservative application interfaces.  The
;; predicates below impose all typing, set, semiring, real-number, content,
;; generated-sigma-algebra, and countable-cover laws explicitly.

(defstub q2631152-apply1 (function argument) t)
(defstub q2631152-apply2 (function left right) t)

(defstub q2631152-r-member-p (real value) t)
(defstub q2631152-r-zero (real) t)
(defstub q2631152-r-one (real) t)
(defstub q2631152-r-add (real left right) t)
(defstub q2631152-r-multiply (real left right) t)
(defstub q2631152-r-negate (real value) t)
(defstub q2631152-r-inverse (real value) t)
(defstub q2631152-r-less (real left right) t)
(defstub q2631152-r-set-member-p (real set value) t)

(defstub q2631152-empty-set (point-carrier) t)
(defstub q2631152-complement-set (point-carrier set) t)
(defstub q2631152-intersection-set (point-carrier left right) t)
(defstub q2631152-difference-set (point-carrier left right) t)
(defstub q2631152-union-set (point-carrier left right) t)
(defstub q2631152-countable-union-set (point-carrier family) t)

;; A Dedekind-complete linearly ordered field presents the real numbers.

(defun q2631152-r-leq (real left right)
  (not (q2631152-r-less real right left)))

(defun-sk q2631152-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2631152-r-member-p real x)
      (q2631152-r-member-p real y)
      (q2631152-r-member-p real z))
     (let* ((zero (q2631152-r-zero real))
            (one (q2631152-r-one real))
            (xy-add (q2631152-r-add real x y))
            (yz-add (q2631152-r-add real y z))
            (xy-mul (q2631152-r-multiply real x y))
            (yz-mul (q2631152-r-multiply real y z))
            (neg-x (q2631152-r-negate real x))
            (inv-x (q2631152-r-inverse real x)))
       (and
        (q2631152-r-member-p real xy-add)
        (q2631152-r-member-p real xy-mul)
        (q2631152-r-member-p real neg-x)
        (q2631152-r-member-p real inv-x)
        (equal
         (q2631152-r-add real xy-add z)
         (q2631152-r-add real x yz-add))
        (equal xy-add (q2631152-r-add real y x))
        (equal (q2631152-r-add real x zero) x)
        (equal (q2631152-r-add real x neg-x) zero)
        (equal
         (q2631152-r-multiply real xy-mul z)
         (q2631152-r-multiply real x yz-mul))
        (equal xy-mul (q2631152-r-multiply real y x))
        (equal (q2631152-r-multiply real x one) x)
        (equal (q2631152-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q2631152-r-multiply real x inv-x)
          one))
        (equal
         (q2631152-r-multiply
          real x (q2631152-r-add real y z))
         (q2631152-r-add
          real
          (q2631152-r-multiply real x y)
          (q2631152-r-multiply real x z))))))))

(defun-sk q2631152-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2631152-r-member-p real x)
      (q2631152-r-member-p real y)
      (q2631152-r-member-p real z))
     (let ((zero (q2631152-r-zero real)))
       (and
        (not (q2631152-r-less real x x))
        (or
         (equal x y)
         (q2631152-r-less real x y)
         (q2631152-r-less real y x))
        (implies
         (and
          (q2631152-r-less real x y)
          (q2631152-r-less real y z))
         (q2631152-r-less real x z))
        (implies
         (q2631152-r-less real x y)
         (q2631152-r-less
          real
          (q2631152-r-add real x z)
          (q2631152-r-add real y z)))
        (implies
         (and
          (q2631152-r-less real zero x)
          (q2631152-r-less real zero y))
         (q2631152-r-less
          real zero
          (q2631152-r-multiply real x y))))))))

(defun-sk q2631152-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q2631152-r-member-p real x)
     (q2631152-r-set-member-p real set x))))

(defun-sk q2631152-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q2631152-r-member-p real x)
      (q2631152-r-set-member-p real set x))
     (q2631152-r-leq real x bound))))

(defun-sk q2631152-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q2631152-r-member-p real bound)
     (q2631152-r-upper-bound-p real set bound))))

(defun-sk q2631152-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q2631152-r-member-p real supremum)
     (q2631152-r-upper-bound-p real set supremum)
     (implies
      (and
       (q2631152-r-member-p real bound)
       (q2631152-r-upper-bound-p real set bound))
      (q2631152-r-leq real supremum bound)))))

(defun-sk q2631152-r-supremum-exists-p (real set)
  (exists (supremum)
    (q2631152-r-supremum-p real set supremum)))

(defun-sk q2631152-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q2631152-r-set-nonempty-p real set)
      (q2631152-r-bounded-above-p real set))
     (q2631152-r-supremum-exists-p real set))))

(defun q2631152-real-field-p (real)
  (let ((zero (q2631152-r-zero real))
        (one (q2631152-r-one real)))
    (and
     (q2631152-r-member-p real zero)
     (q2631152-r-member-p real one)
     (not (equal zero one))
     (q2631152-r-less real zero one)
     (q2631152-r-field-laws-p real)
     (q2631152-r-order-laws-p real)
     (q2631152-r-dedekind-complete-p real))))

;; Extended nonnegative reals are represented canonically by a nonnegative
;; real value or a distinguished top element.

(defun q2631152-ennreal-finite (real value)
  (list :q2631152-finite real value))

(defun q2631152-ennreal-top (real)
  (list :q2631152-top real))

(defun q2631152-ennreal-zero (real)
  (q2631152-ennreal-finite real (q2631152-r-zero real)))

(defun q2631152-ennreal-finite-p (real value)
  (and
   (true-listp value)
   (equal (len value) 3)
   (equal (car value) :q2631152-finite)
   (equal (cadr value) real)
   (q2631152-r-member-p real (caddr value))
   (q2631152-r-leq
    real (q2631152-r-zero real) (caddr value))))

(defun q2631152-ennreal-p (real value)
  (or
   (equal value (q2631152-ennreal-top real))
   (q2631152-ennreal-finite-p real value)))

(defun q2631152-ennreal-leq (real left right)
  (cond
   ((equal right (q2631152-ennreal-top real)) t)
   ((equal left (q2631152-ennreal-top real)) nil)
   (t
    (q2631152-r-leq real (caddr left) (caddr right)))))

(defun q2631152-ennreal-add (real left right)
  (if
      (or
       (equal left (q2631152-ennreal-top real))
       (equal right (q2631152-ennreal-top real)))
      (q2631152-ennreal-top real)
    (q2631152-ennreal-finite
     real
     (q2631152-r-add real (caddr left) (caddr right)))))

;; Arbitrary subsets of the point carrier and their operations.

(defun q2631152-point-member-p (point-carrier value)
  (if (q2631152-apply1 point-carrier value) t nil))

(defun-sk q2631152-set-p (point-carrier set)
  (forall (x)
    (implies
     (q2631152-apply1 set x)
     (q2631152-point-member-p point-carrier x))))

(defun-sk q2631152-set-equivalent-p
    (point-carrier left right)
  (forall (x)
    (implies
     (q2631152-point-member-p point-carrier x)
     (iff
      (q2631152-apply1 left x)
      (q2631152-apply1 right x)))))

(defun-sk q2631152-subset-p
    (point-carrier left right)
  (forall (x)
    (implies
     (and
      (q2631152-point-member-p point-carrier x)
      (q2631152-apply1 left x))
     (q2631152-apply1 right x))))

(defun-sk q2631152-disjoint-p
    (point-carrier left right)
  (forall (x)
    (implies
     (q2631152-point-member-p point-carrier x)
     (not
      (and
       (q2631152-apply1 left x)
       (q2631152-apply1 right x))))))

(defun-sk q2631152-family-values-are-sets-p
    (point-carrier family)
  (forall (n)
    (implies
     (natp n)
     (q2631152-set-p
      point-carrier (q2631152-apply1 family n)))))

(defun-sk q2631152-family-member-exists-p (family x)
  (exists (n)
    (and
     (natp n)
     (q2631152-apply1 (q2631152-apply1 family n) x))))

(defun-sk q2631152-set-extensionality-p (point-carrier)
  (forall (left right)
    (implies
     (and
      (q2631152-set-p point-carrier left)
      (q2631152-set-p point-carrier right)
      (q2631152-set-equivalent-p point-carrier left right))
     (equal left right))))

(defun-sk q2631152-basic-set-operation-laws-p (point-carrier)
  (forall (left right x)
    (and
     (q2631152-set-p
      point-carrier (q2631152-empty-set point-carrier))
     (implies
      (q2631152-point-member-p point-carrier x)
      (not
       (q2631152-apply1
        (q2631152-empty-set point-carrier) x)))
     (implies
      (q2631152-set-p point-carrier left)
      (and
       (q2631152-set-p
        point-carrier
        (q2631152-complement-set point-carrier left))
       (implies
        (q2631152-point-member-p point-carrier x)
        (iff
         (q2631152-apply1
          (q2631152-complement-set point-carrier left) x)
         (not (q2631152-apply1 left x))))))
     (implies
      (and
       (q2631152-set-p point-carrier left)
       (q2631152-set-p point-carrier right))
      (and
       (q2631152-set-p
        point-carrier
        (q2631152-intersection-set
         point-carrier left right))
       (q2631152-set-p
        point-carrier
        (q2631152-difference-set point-carrier left right))
       (q2631152-set-p
        point-carrier
        (q2631152-union-set point-carrier left right))
       (implies
        (q2631152-point-member-p point-carrier x)
        (and
         (iff
          (q2631152-apply1
           (q2631152-intersection-set
            point-carrier left right)
           x)
          (and
           (q2631152-apply1 left x)
           (q2631152-apply1 right x)))
         (iff
          (q2631152-apply1
           (q2631152-difference-set
            point-carrier left right)
           x)
          (and
           (q2631152-apply1 left x)
           (not (q2631152-apply1 right x))))
         (iff
          (q2631152-apply1
           (q2631152-union-set point-carrier left right)
           x)
          (or
           (q2631152-apply1 left x)
           (q2631152-apply1 right x))))))))))

(defun-sk q2631152-countable-union-laws-p (point-carrier)
  (forall (family x)
    (implies
     (q2631152-family-values-are-sets-p
      point-carrier family)
     (and
      (q2631152-set-p
       point-carrier
       (q2631152-countable-union-set
        point-carrier family))
      (implies
       (q2631152-point-member-p point-carrier x)
       (iff
        (q2631152-apply1
         (q2631152-countable-union-set
          point-carrier family)
         x)
        (q2631152-family-member-exists-p family x)))))))

(defun q2631152-set-interface-p (point-carrier)
  (and
   (q2631152-set-extensionality-p point-carrier)
   (q2631152-basic-set-operation-laws-p point-carrier)
   (q2631152-countable-union-laws-p point-carrier)))

;; Finite lists represent the genuinely finite decompositions in the source
;; definition of a semiring of sets and of finite additivity.

(defun q2631152-set-list-p (point-carrier sets)
  (declare (xargs :measure (acl2-count sets)))
  (if (endp sets)
      (equal sets nil)
    (and
     (q2631152-set-p point-carrier (car sets))
     (q2631152-set-list-p point-carrier (cdr sets)))))

(defun q2631152-all-in-family-p (family sets)
  (declare (xargs :measure (acl2-count sets)))
  (if (endp sets)
      (equal sets nil)
    (and
     (q2631152-apply1 family (car sets))
     (q2631152-all-in-family-p family (cdr sets)))))

(defun q2631152-disjoint-from-list-p
    (point-carrier set sets)
  (declare (xargs :measure (acl2-count sets)))
  (if (endp sets)
      (equal sets nil)
    (and
     (q2631152-disjoint-p
      point-carrier set (car sets))
     (q2631152-disjoint-from-list-p
      point-carrier set (cdr sets)))))

(defun q2631152-pairwise-disjoint-list-p
    (point-carrier sets)
  (declare (xargs :measure (acl2-count sets)))
  (if (endp sets)
      (equal sets nil)
    (and
     (q2631152-disjoint-from-list-p
      point-carrier (car sets) (cdr sets))
     (q2631152-pairwise-disjoint-list-p
      point-carrier (cdr sets)))))

(defun q2631152-finite-union
    (point-carrier sets)
  (declare (xargs :measure (acl2-count sets)))
  (if (endp sets)
      (q2631152-empty-set point-carrier)
    (q2631152-union-set
     point-carrier
     (car sets)
     (q2631152-finite-union point-carrier (cdr sets)))))

(defun q2631152-finite-content-sum
    (real content sets)
  (declare (xargs :measure (acl2-count sets)))
  (if (endp sets)
      (q2631152-ennreal-zero real)
    (q2631152-ennreal-add
     real
     (q2631152-apply1 content (car sets))
     (q2631152-finite-content-sum
      real content (cdr sets)))))

;; A semiring contains the empty set, is closed under intersection, and each
;; difference is a finite pairwise-disjoint union of semiring members.

(defun-sk q2631152-difference-decomposition-exists-p
    (point-carrier semiring left right)
  (exists (parts)
    (and
     (true-listp parts)
     (no-duplicatesp-equal parts)
     (q2631152-set-list-p point-carrier parts)
     (q2631152-all-in-family-p semiring parts)
     (q2631152-pairwise-disjoint-list-p
      point-carrier parts)
     (equal
      (q2631152-difference-set
       point-carrier left right)
      (q2631152-finite-union point-carrier parts)))))

(defun-sk q2631152-semiring-members-are-sets-p
    (point-carrier semiring)
  (forall (set)
    (implies
     (q2631152-apply1 semiring set)
     (q2631152-set-p point-carrier set))))

(defun-sk q2631152-semiring-closure-p
    (point-carrier semiring)
  (forall (left right)
    (implies
     (and
      (q2631152-apply1 semiring left)
      (q2631152-apply1 semiring right))
     (and
      (q2631152-apply1
       semiring
       (q2631152-intersection-set
        point-carrier left right))
      (q2631152-difference-decomposition-exists-p
       point-carrier semiring left right)))))

(defun q2631152-set-semiring-p
    (point-carrier semiring)
  (and
   (q2631152-semiring-members-are-sets-p
    point-carrier semiring)
   (q2631152-apply1
    semiring (q2631152-empty-set point-carrier))
   (q2631152-semiring-closure-p
    point-carrier semiring)))

;; The given measurable space is exactly the sigma algebra generated by the
;; semiring, expressed by its universal minimality property.

(defun-sk q2631152-sigma-members-are-sets-p
    (point-carrier sigma)
  (forall (set)
    (implies
     (q2631152-apply1 sigma set)
     (q2631152-set-p point-carrier set))))

(defun-sk q2631152-family-values-in-sigma-p
    (sigma family)
  (forall (n)
    (implies
     (natp n)
     (q2631152-apply1
      sigma (q2631152-apply1 family n)))))

(defun-sk q2631152-sigma-closure-p
    (point-carrier sigma)
  (forall (set family)
    (and
     (implies
      (q2631152-apply1 sigma set)
      (q2631152-apply1
       sigma
       (q2631152-complement-set point-carrier set)))
     (implies
      (and
       (q2631152-family-values-are-sets-p
        point-carrier family)
       (q2631152-family-values-in-sigma-p sigma family))
      (q2631152-apply1
       sigma
       (q2631152-countable-union-set
        point-carrier family))))))

(defun q2631152-sigma-algebra-p
    (point-carrier sigma)
  (and
   (q2631152-sigma-members-are-sets-p
    point-carrier sigma)
   (q2631152-apply1
    sigma (q2631152-empty-set point-carrier))
   (q2631152-sigma-closure-p point-carrier sigma)))

(defun-sk q2631152-family-subset-p (left right)
  (forall (set)
    (implies
     (q2631152-apply1 left set)
     (q2631152-apply1 right set))))

(defun-sk q2631152-generated-minimal-p
    (point-carrier semiring measurable-space)
  (forall (other)
    (implies
     (and
      (q2631152-sigma-algebra-p
       point-carrier other)
      (q2631152-family-subset-p semiring other))
     (q2631152-family-subset-p
      measurable-space other))))

(defun q2631152-generated-measurable-space-p
    (point-carrier semiring measurable-space)
  (and
   (q2631152-sigma-algebra-p
    point-carrier measurable-space)
   (q2631152-family-subset-p
    semiring measurable-space)
   (q2631152-generated-minimal-p
    point-carrier semiring measurable-space)))

;; Countable sums in ENNReal are least upper bounds of their finite partial
;; sums.

(defun q2631152-series-partial-sum
    (real values count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q2631152-ennreal-zero real)
    (q2631152-ennreal-add
     real
     (q2631152-series-partial-sum
      real values (1- count))
     (q2631152-apply1 values (1- count)))))

(defun-sk q2631152-series-values-p (real values)
  (forall (n)
    (implies
     (natp n)
     (q2631152-ennreal-p
      real (q2631152-apply1 values n)))))

(defun-sk q2631152-series-upper-bound-p
    (real values bound)
  (forall (count)
    (implies
     (natp count)
     (q2631152-ennreal-leq
      real
      (q2631152-series-partial-sum
       real values count)
      bound))))

(defun-sk q2631152-series-sum-p
    (real values total)
  (forall (bound)
    (and
     (q2631152-series-values-p real values)
     (q2631152-ennreal-p real total)
     (q2631152-series-upper-bound-p
      real values total)
     (implies
      (and
       (q2631152-ennreal-p real bound)
       (q2631152-series-upper-bound-p
        real values bound))
      (q2631152-ennreal-leq
       real total bound)))))

;; An AddContent is zero on the empty set and finitely additive on finite
;; pairwise-disjoint semiring families whose union is in the semiring.

(defun-sk q2631152-content-values-p
    (real point-carrier content)
  (forall (set)
    (implies
     (q2631152-set-p point-carrier set)
     (q2631152-ennreal-p
      real (q2631152-apply1 content set)))))

(defun-sk q2631152-content-finite-additivity-p
    (real point-carrier semiring content)
  (forall (parts)
    (implies
     (and
      (true-listp parts)
      (no-duplicatesp-equal parts)
      (q2631152-set-list-p point-carrier parts)
      (q2631152-all-in-family-p semiring parts)
      (q2631152-pairwise-disjoint-list-p
       point-carrier parts)
      (q2631152-apply1
       semiring
       (q2631152-finite-union
        point-carrier parts)))
     (equal
      (q2631152-apply1
       content
       (q2631152-finite-union
        point-carrier parts))
      (q2631152-finite-content-sum
       real content parts)))))

(defun q2631152-add-content-p
    (real point-carrier semiring content)
  (and
   (q2631152-content-values-p
    real point-carrier content)
   (equal
    (q2631152-apply1
     content (q2631152-empty-set point-carrier))
    (q2631152-ennreal-zero real))
   (q2631152-content-finite-additivity-p
    real point-carrier semiring content)))

(defun-sk q2631152-content-family-values-p
    (real content family values)
  (forall (n)
    (implies
     (natp n)
     (equal
      (q2631152-apply1 values n)
      (q2631152-apply1
       content (q2631152-apply1 family n))))))

(defun-sk q2631152-content-series-sum-exists-p
    (real content family)
  (exists (values total)
    (and
     (q2631152-content-family-values-p
      real content family values)
     (q2631152-series-sum-p real values total))))

(defun-sk q2631152-content-series-bounds-union-p
    (real point-carrier content family union)
  (exists (values total)
    (and
     (q2631152-content-family-values-p
      real content family values)
     (q2631152-series-sum-p real values total)
     (q2631152-ennreal-leq
      real
      (q2631152-apply1 content union)
      total))))

(defun-sk q2631152-sigma-subadditive-content-p
    (real point-carrier semiring content)
  (forall (family)
    (implies
     (and
      (q2631152-family-values-are-sets-p
       point-carrier family)
      (q2631152-family-values-in-sigma-p
       semiring family)
      (q2631152-apply1
       semiring
       (q2631152-countable-union-set
        point-carrier family)))
     (q2631152-content-series-bounds-union-p
      real
      point-carrier
      content
      family
      (q2631152-countable-union-set
       point-carrier family)))))

;; The induced outer-measure value is the infimum of the sums of all
;; countable semiring covers.  This is the value used by the Carathéodory
;; measure and by its trim to the generated measurable space.

(defun-sk q2631152-family-covers-set-p
    (point-carrier family target)
  (forall (x)
    (implies
     (and
      (q2631152-point-member-p point-carrier x)
      (q2631152-apply1 target x))
     (q2631152-apply1
      (q2631152-countable-union-set
       point-carrier family)
      x))))

(defun q2631152-cover-cost-p
    (real point-carrier semiring content target
     family values total)
  (and
   (q2631152-family-values-are-sets-p
    point-carrier family)
   (q2631152-family-values-in-sigma-p
    semiring family)
   (q2631152-family-covers-set-p
    point-carrier family target)
   (q2631152-content-family-values-p
    real content family values)
   (q2631152-series-sum-p real values total)))

(defun-sk q2631152-cover-cost-lower-bound-p
    (real point-carrier semiring content target lower)
  (forall (family values total)
    (implies
     (q2631152-cover-cost-p
      real point-carrier semiring content target
      family values total)
     (q2631152-ennreal-leq real lower total))))

(defun-sk q2631152-induced-outer-measure-value-p
    (real point-carrier semiring content target value)
  (forall (lower)
    (and
     (q2631152-ennreal-p real value)
     (q2631152-cover-cost-lower-bound-p
      real point-carrier semiring content target value)
     (implies
      (and
       (q2631152-ennreal-p real lower)
       (q2631152-cover-cost-lower-bound-p
        real point-carrier semiring content target lower))
      (q2631152-ennreal-leq real lower value)))))

(defun q2631152-constructed-measure-value-p
    (real point-carrier semiring measurable-space
     content target value)
  (and
   (q2631152-apply1 measurable-space target)
   (q2631152-induced-outer-measure-value-p
    real point-carrier semiring content target value)))

(defun-sk q2631152-constructed-measure-agrees-p
    (real point-carrier semiring measurable-space
     content target)
  (exists (value)
    (and
     (q2631152-constructed-measure-value-p
      real point-carrier semiring measurable-space
      content target value)
     (equal value (q2631152-apply1 content target)))))

(defun-sk
    thousand-theorems-q2631152-caratheodorys-extension-theorem-statement
    ()
  (forall
    (real point-carrier semiring measurable-space content target)
    (implies
     (and
      (q2631152-real-field-p real)
      (q2631152-set-interface-p point-carrier)
      (q2631152-set-semiring-p
       point-carrier semiring)
      (q2631152-generated-measurable-space-p
       point-carrier semiring measurable-space)
      (q2631152-add-content-p
       real point-carrier semiring content)
      (q2631152-sigma-subadditive-content-p
       real point-carrier semiring content)
      (q2631152-apply1 semiring target))
     (q2631152-constructed-measure-agrees-p
      real point-carrier semiring measurable-space
      content target))))

(value-triple :itpeval-statement-checked)
:q
