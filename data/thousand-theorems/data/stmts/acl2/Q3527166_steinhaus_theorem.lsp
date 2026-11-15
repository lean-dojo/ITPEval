;; Statement-only formalization of thousand-theorems corpus artifact Q3527166,
;; "Steinhaus theorem": in a locally compact topological group, the quotient
;; E/E of a measurable positive-measure set is a neighborhood of the identity
;; for every inner-regular left Haar measure. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The interfaces below present arbitrary carriers, sets, indexed families,
;; group operations, topologies, Borel sigma algebras, and measures.  Every
;; structural law used by the source declaration is an explicit hypothesis of
;; the final predicate.  Extended nonnegative reals are represented exactly as
;; a nonnegative element of a Dedekind-complete ordered field or a top element.

;; A presentation of the real field.

(defstub q3527166-r-member-p (real value) t)
(defstub q3527166-r-zero (real) t)
(defstub q3527166-r-one (real) t)
(defstub q3527166-r-add (real left right) t)
(defstub q3527166-r-multiply (real left right) t)
(defstub q3527166-r-negate (real value) t)
(defstub q3527166-r-inverse (real value) t)
(defstub q3527166-r-less (real left right) t)
(defstub q3527166-r-subset-member-p (real subset value) t)

(defun q3527166-r-leq (real left right)
  (not (q3527166-r-less real right left)))

(defun-sk q3527166-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3527166-r-member-p real x)
      (q3527166-r-member-p real y)
      (q3527166-r-member-p real z))
     (let* ((zero (q3527166-r-zero real))
            (one (q3527166-r-one real))
            (xy-add (q3527166-r-add real x y))
            (yz-add (q3527166-r-add real y z))
            (xy-mul (q3527166-r-multiply real x y))
            (yz-mul (q3527166-r-multiply real y z))
            (neg-x (q3527166-r-negate real x))
            (inv-x (q3527166-r-inverse real x)))
       (and
        (q3527166-r-member-p real xy-add)
        (q3527166-r-member-p real xy-mul)
        (q3527166-r-member-p real neg-x)
        (q3527166-r-member-p real inv-x)
        (equal
         (q3527166-r-add real xy-add z)
         (q3527166-r-add real x yz-add))
        (equal xy-add (q3527166-r-add real y x))
        (equal (q3527166-r-add real x zero) x)
        (equal (q3527166-r-add real x neg-x) zero)
        (equal
         (q3527166-r-multiply real xy-mul z)
         (q3527166-r-multiply real x yz-mul))
        (equal xy-mul (q3527166-r-multiply real y x))
        (equal (q3527166-r-multiply real x one) x)
        (equal (q3527166-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q3527166-r-multiply real x inv-x)
          one))
        (equal
         (q3527166-r-multiply
          real x (q3527166-r-add real y z))
         (q3527166-r-add
          real
          (q3527166-r-multiply real x y)
          (q3527166-r-multiply real x z))))))))

(defun-sk q3527166-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3527166-r-member-p real x)
      (q3527166-r-member-p real y)
      (q3527166-r-member-p real z))
     (let ((zero (q3527166-r-zero real)))
       (and
        (not (q3527166-r-less real x x))
        (or
         (equal x y)
         (q3527166-r-less real x y)
         (q3527166-r-less real y x))
        (implies
         (and
          (q3527166-r-less real x y)
          (q3527166-r-less real y z))
         (q3527166-r-less real x z))
        (implies
         (q3527166-r-less real x y)
         (q3527166-r-less
          real
          (q3527166-r-add real x z)
          (q3527166-r-add real y z)))
        (implies
         (and
          (q3527166-r-less real zero x)
          (q3527166-r-less real zero y))
         (q3527166-r-less
          real zero
          (q3527166-r-multiply real x y))))))))

(defun-sk q3527166-r-subset-nonempty-p (real subset)
  (exists (x)
    (and
     (q3527166-r-member-p real x)
     (q3527166-r-subset-member-p real subset x))))

(defun-sk q3527166-r-upper-bound-p (real subset bound)
  (forall (x)
    (implies
     (and
      (q3527166-r-member-p real x)
      (q3527166-r-subset-member-p real subset x))
     (q3527166-r-leq real x bound))))

(defun-sk q3527166-r-bounded-above-p (real subset)
  (exists (bound)
    (and
     (q3527166-r-member-p real bound)
     (q3527166-r-upper-bound-p real subset bound))))

(defun-sk q3527166-r-supremum-p (real subset supremum)
  (forall (bound)
    (and
     (q3527166-r-member-p real supremum)
     (q3527166-r-upper-bound-p real subset supremum)
     (implies
      (and
       (q3527166-r-member-p real bound)
       (q3527166-r-upper-bound-p real subset bound))
      (q3527166-r-leq real supremum bound)))))

(defun-sk q3527166-r-has-supremum-p (real subset)
  (exists (supremum)
    (q3527166-r-supremum-p real subset supremum)))

(defun-sk q3527166-r-dedekind-complete-p (real)
  (forall (subset)
    (implies
     (and
      (q3527166-r-subset-nonempty-p real subset)
      (q3527166-r-bounded-above-p real subset))
     (q3527166-r-has-supremum-p real subset))))

(defun q3527166-real-field-p (real)
  (let ((zero (q3527166-r-zero real))
        (one (q3527166-r-one real)))
    (and
     (q3527166-r-member-p real zero)
     (q3527166-r-member-p real one)
     (not (equal zero one))
     (q3527166-r-field-laws-p real)
     (q3527166-r-order-laws-p real)
     (q3527166-r-less real zero one)
     (q3527166-r-dedekind-complete-p real))))

;; The extended nonnegative reals over this real-field presentation.

(defun q3527166-enn-zero (real)
  (list :finite (q3527166-r-zero real)))

(defun q3527166-enn-top ()
  (list :top))

(defun q3527166-enn-finite (value)
  (list :finite value))

(defun q3527166-enn-finite-p (real value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :finite)
   (q3527166-r-member-p real (cadr value))
   (q3527166-r-leq
    real (q3527166-r-zero real) (cadr value))))

(defun q3527166-enn-p (real value)
  (or
   (equal value (q3527166-enn-top))
   (q3527166-enn-finite-p real value)))

(defun q3527166-enn-less (real left right)
  (cond
   ((equal left (q3527166-enn-top)) nil)
   ((equal right (q3527166-enn-top))
    (q3527166-enn-finite-p real left))
   ((and
     (q3527166-enn-finite-p real left)
     (q3527166-enn-finite-p real right))
    (q3527166-r-less real (cadr left) (cadr right)))
   (t nil)))

(defun q3527166-enn-leq (real left right)
  (not (q3527166-enn-less real right left)))

(defun q3527166-enn-add (real left right)
  (if (and
       (q3527166-enn-finite-p real left)
       (q3527166-enn-finite-p real right))
      (q3527166-enn-finite
       (q3527166-r-add real (cadr left) (cadr right)))
    (q3527166-enn-top)))

;; Arbitrary groups and arbitrary subsets of their carrier.

(defstub q3527166-carrier-p (group value) t)
(defstub q3527166-one (group) t)
(defstub q3527166-mul (group left right) t)
(defstub q3527166-inv (group value) t)

(defstub q3527166-set-member-p (group set value) t)
(defstub q3527166-empty-set (group) t)
(defstub q3527166-univ-set (group) t)
(defstub q3527166-inter-set (group left right) t)
(defstub q3527166-union-set (group left right) t)
(defstub q3527166-complement-set (group set) t)
(defstub q3527166-family-member-p (family set) t)
(defstub q3527166-family-union-set (group family) t)
(defstub q3527166-sequence-set (sequence index) t)
(defstub q3527166-sequence-union-set (group sequence) t)
(defstub q3527166-left-translate-set (group element set) t)

(defun-sk q3527166-set-p (group set)
  (forall (x)
    (implies
     (q3527166-set-member-p group set x)
     (q3527166-carrier-p group x))))

(defun-sk q3527166-subset-p (group left right)
  (forall (x)
    (implies
     (q3527166-set-member-p group left x)
     (q3527166-set-member-p group right x))))

(defun q3527166-set-equiv-p (group left right)
  (and
   (q3527166-subset-p group left right)
   (q3527166-subset-p group right left)))

(defun-sk q3527166-set-nonempty-p (group set)
  (exists (x)
    (q3527166-set-member-p group set x)))

(defun-sk q3527166-disjoint-p (group left right)
  (forall (x)
    (not
     (and
      (q3527166-set-member-p group left x)
      (q3527166-set-member-p group right x)))))

(defun-sk q3527166-family-union-member-p (group family x)
  (exists (set)
    (and
     (q3527166-family-member-p family set)
     (q3527166-set-member-p group set x))))

(defun-sk q3527166-sequence-union-member-p (group sequence x)
  (exists (n)
    (and
     (natp n)
     (q3527166-set-member-p
      group (q3527166-sequence-set sequence n) x))))

(defun-sk q3527166-left-translate-member-p
    (group element set x)
  (exists (y)
    (and
     (q3527166-carrier-p group y)
     (q3527166-set-member-p group set y)
     (equal x (q3527166-mul group element y)))))

(defun-sk q3527166-empty-univ-laws-p (group)
  (forall (x)
    (and
     (not
      (q3527166-set-member-p
       group (q3527166-empty-set group) x))
     (iff
      (q3527166-set-member-p
       group (q3527166-univ-set group) x)
      (q3527166-carrier-p group x)))))

(defun-sk q3527166-binary-set-laws-p (group)
  (forall (x left right)
    (and
     (iff
      (q3527166-set-member-p
       group (q3527166-inter-set group left right) x)
      (and
       (q3527166-set-member-p group left x)
       (q3527166-set-member-p group right x)))
     (iff
      (q3527166-set-member-p
       group (q3527166-union-set group left right) x)
      (or
       (q3527166-set-member-p group left x)
       (q3527166-set-member-p group right x))))))

(defun-sk q3527166-complement-law-p (group)
  (forall (x set)
    (iff
     (q3527166-set-member-p
      group (q3527166-complement-set group set) x)
     (and
      (q3527166-carrier-p group x)
      (not (q3527166-set-member-p group set x))))))

(defun-sk q3527166-family-union-law-p (group)
  (forall (x family)
    (iff
     (q3527166-set-member-p
      group (q3527166-family-union-set group family) x)
     (q3527166-family-union-member-p group family x))))

(defun-sk q3527166-sequence-union-law-p (group)
  (forall (x sequence)
    (iff
     (q3527166-set-member-p
      group (q3527166-sequence-union-set group sequence) x)
     (q3527166-sequence-union-member-p group sequence x))))

(defun-sk q3527166-left-translate-law-p (group)
  (forall (x element set)
    (implies
     (q3527166-carrier-p group element)
     (iff
      (q3527166-set-member-p
       group
       (q3527166-left-translate-set group element set)
       x)
      (q3527166-left-translate-member-p
       group element set x)))))

(defun q3527166-set-operation-laws-p (group)
  (and
   (q3527166-empty-univ-laws-p group)
   (q3527166-binary-set-laws-p group)
   (q3527166-complement-law-p group)
   (q3527166-family-union-law-p group)
   (q3527166-sequence-union-law-p group)
   (q3527166-left-translate-law-p group)))

(defun-sk q3527166-group-laws-p (group)
  (forall (x y z)
    (implies
     (and
      (q3527166-carrier-p group x)
      (q3527166-carrier-p group y)
      (q3527166-carrier-p group z))
     (let ((one (q3527166-one group))
           (xy (q3527166-mul group x y))
           (yz (q3527166-mul group y z))
           (x-inv (q3527166-inv group x)))
       (and
        (q3527166-carrier-p group one)
        (q3527166-carrier-p group xy)
        (q3527166-carrier-p group x-inv)
        (equal
         (q3527166-mul group xy z)
         (q3527166-mul group x yz))
        (equal (q3527166-mul group one x) x)
        (equal (q3527166-mul group x one) x)
        (equal (q3527166-mul group x-inv x) one)
        (equal (q3527166-mul group x x-inv) one))))))

;; Topological spaces and compact subsets.

(defstub q3527166-open-p (topology group set) t)

(defun-sk q3527166-open-family-p (topology group family)
  (forall (set)
    (implies
     (q3527166-family-member-p family set)
     (q3527166-open-p topology group set))))

(defun-sk q3527166-topology-laws-p (topology group)
  (forall (left right family)
    (and
     (implies
      (q3527166-open-p topology group left)
      (q3527166-set-p group left))
     (implies
      (and
       (q3527166-set-equiv-p group left right)
       (q3527166-open-p topology group left))
      (q3527166-open-p topology group right))
     (q3527166-open-p
      topology group (q3527166-empty-set group))
     (q3527166-open-p
      topology group (q3527166-univ-set group))
     (implies
      (and
       (q3527166-open-p topology group left)
       (q3527166-open-p topology group right))
      (q3527166-open-p
       topology group
       (q3527166-inter-set group left right)))
     (implies
      (q3527166-open-family-p topology group family)
      (q3527166-open-p
       topology group
       (q3527166-family-union-set group family))))))

(defun q3527166-member-of-set-list-p (group sets x)
  (if (consp sets)
      (or
       (q3527166-set-member-p group (car sets) x)
       (q3527166-member-of-set-list-p group (cdr sets) x))
    nil))

(defun q3527166-list-from-family-p (family sets)
  (if (consp sets)
      (and
       (q3527166-family-member-p family (car sets))
       (q3527166-list-from-family-p family (cdr sets)))
    (equal sets nil)))

(defun-sk q3527166-list-covers-p (group sets covered)
  (forall (x)
    (implies
     (q3527166-set-member-p group covered x)
     (q3527166-member-of-set-list-p group sets x))))

(defun-sk q3527166-finite-subcover-exists-p
    (group family covered)
  (exists (sets)
    (and
     (true-listp sets)
     (q3527166-list-from-family-p family sets)
     (q3527166-list-covers-p group sets covered))))

(defun-sk q3527166-compact-p (topology group set)
  (forall (family)
    (implies
     (and
      (q3527166-open-family-p topology group family)
      (q3527166-subset-p
       group set
       (q3527166-family-union-set group family)))
     (q3527166-finite-subcover-exists-p
      group family set))))

(defun-sk q3527166-compact-extensional-p (topology group)
  (forall (left right)
    (implies
     (q3527166-set-equiv-p group left right)
     (iff
      (q3527166-compact-p topology group left)
      (q3527166-compact-p topology group right)))))

(defun-sk q3527166-mul-neighborhood-product-p
    (group left-neighborhood right-neighborhood open-set)
  (forall (left right)
    (implies
     (and
      (q3527166-set-member-p group left-neighborhood left)
      (q3527166-set-member-p group right-neighborhood right))
     (q3527166-set-member-p
      group open-set
      (q3527166-mul group left right)))))

(defun-sk q3527166-mul-continuous-at-p
    (topology group x y open-set)
  (exists (left-neighborhood right-neighborhood)
    (and
     (q3527166-open-p topology group left-neighborhood)
     (q3527166-open-p topology group right-neighborhood)
     (q3527166-set-member-p group left-neighborhood x)
     (q3527166-set-member-p group right-neighborhood y)
     (q3527166-subset-p
      group
      (q3527166-left-translate-set
       group x right-neighborhood)
      open-set)
     ;; The following universally quantified condition is the exact
     ;; V*W subset U condition; the displayed translate subset is retained
     ;; only as a useful well-typed special case.
     (q3527166-mul-neighborhood-product-p
      group left-neighborhood right-neighborhood open-set))))

(defun-sk q3527166-inv-neighborhood-p
    (group neighborhood open-set)
  (forall (x)
    (implies
     (q3527166-set-member-p group neighborhood x)
     (q3527166-set-member-p
      group open-set (q3527166-inv group x)))))

(defun-sk q3527166-inv-continuous-at-p
    (topology group x open-set)
  (exists (neighborhood)
    (and
     (q3527166-open-p topology group neighborhood)
     (q3527166-set-member-p group neighborhood x)
     (q3527166-inv-neighborhood-p
      group neighborhood open-set))))

(defun-sk q3527166-topological-group-p (topology group)
  (forall (x y open-set)
    (implies
     (and
      (q3527166-carrier-p group x)
      (q3527166-carrier-p group y)
      (q3527166-open-p topology group open-set))
     (and
      (implies
       (q3527166-set-member-p
        group open-set (q3527166-mul group x y))
       (q3527166-mul-continuous-at-p
        topology group x y open-set))
      (implies
       (q3527166-set-member-p
        group open-set (q3527166-inv group x))
       (q3527166-inv-continuous-at-p
        topology group x open-set))))))

(defun-sk q3527166-compact-neighborhood-inside-p
    (topology group x open-set)
  (exists (neighborhood compact-set)
    (and
     (q3527166-open-p topology group neighborhood)
     (q3527166-set-member-p group neighborhood x)
     (q3527166-compact-p topology group compact-set)
     (q3527166-subset-p group neighborhood compact-set)
     (q3527166-subset-p group compact-set open-set))))

(defun-sk q3527166-locally-compact-p (topology group)
  (forall (x open-set)
    (implies
     (and
      (q3527166-carrier-p group x)
      (q3527166-open-p topology group open-set)
      (q3527166-set-member-p group open-set x))
     (q3527166-compact-neighborhood-inside-p
      topology group x open-set))))

;; Borel measurable spaces.

(defstub q3527166-measurable-p (measurable-space group set) t)

(defun-sk q3527166-measurable-sequence-p
    (measurable-space group sequence)
  (forall (n)
    (implies
     (natp n)
     (q3527166-measurable-p
      measurable-space group
      (q3527166-sequence-set sequence n)))))

(defun-sk q3527166-sequence-in-family-p (family sequence)
  (forall (n)
    (implies
     (natp n)
     (q3527166-family-member-p
      family (q3527166-sequence-set sequence n)))))

(defun-sk q3527166-sigma-family-p (group family)
  (forall (left right sequence)
    (and
     (implies
      (q3527166-family-member-p family left)
      (q3527166-set-p group left))
     (implies
      (and
       (q3527166-set-equiv-p group left right)
       (q3527166-family-member-p family left))
      (q3527166-family-member-p family right))
     (q3527166-family-member-p
      family (q3527166-empty-set group))
     (implies
      (q3527166-family-member-p family left)
      (q3527166-family-member-p
       family (q3527166-complement-set group left)))
     (implies
      (q3527166-sequence-in-family-p family sequence)
      (q3527166-family-member-p
       family
       (q3527166-sequence-union-set group sequence))))))

(defun-sk q3527166-measurable-space-laws-p
    (measurable-space group)
  (forall (left right sequence)
    (and
     (implies
      (q3527166-measurable-p measurable-space group left)
      (q3527166-set-p group left))
     (implies
      (and
       (q3527166-set-equiv-p group left right)
       (q3527166-measurable-p measurable-space group left))
      (q3527166-measurable-p measurable-space group right))
     (q3527166-measurable-p
      measurable-space group (q3527166-empty-set group))
     (implies
      (q3527166-measurable-p measurable-space group left)
      (q3527166-measurable-p
       measurable-space group
       (q3527166-complement-set group left)))
     (implies
      (q3527166-measurable-sequence-p
       measurable-space group sequence)
      (q3527166-measurable-p
       measurable-space group
       (q3527166-sequence-union-set group sequence))))))

(defun-sk q3527166-opens-in-family-p
    (topology group family)
  (forall (set)
    (implies
     (q3527166-open-p topology group set)
     (q3527166-family-member-p family set))))

(defun-sk q3527166-opens-measurable-p
    (topology measurable-space group)
  (forall (set)
    (implies
     (q3527166-open-p topology group set)
     (q3527166-measurable-p measurable-space group set))))

(defun-sk q3527166-measurables-in-family-p
    (measurable-space group family)
  (forall (set)
    (implies
     (q3527166-measurable-p measurable-space group set)
     (q3527166-family-member-p family set))))

(defun-sk q3527166-borel-minimal-p
    (topology measurable-space group)
  (forall (family)
    (implies
     (and
      (q3527166-sigma-family-p group family)
      (q3527166-opens-in-family-p topology group family))
     (q3527166-measurables-in-family-p
      measurable-space group family))))

(defun q3527166-borel-space-p
    (topology measurable-space group)
  (and
   (q3527166-measurable-space-laws-p measurable-space group)
   (q3527166-opens-measurable-p
    topology measurable-space group)
   (q3527166-borel-minimal-p
    topology measurable-space group)))

;; Measures with values in the extended nonnegative reals.

(defstub q3527166-measure-value (measure set) t)

(defun-sk q3527166-increasing-sequence-p (group sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (<= m n))
     (q3527166-subset-p
      group
      (q3527166-sequence-set sequence m)
      (q3527166-sequence-set sequence n)))))

(defun-sk q3527166-measure-values-p
    (real group measure)
  (forall (set)
    (implies
     (q3527166-set-p group set)
     (q3527166-enn-p
      real (q3527166-measure-value measure set)))))

(defun-sk q3527166-measure-extensional-p
    (group measure)
  (forall (left right)
    (implies
     (q3527166-set-equiv-p group left right)
     (equal
      (q3527166-measure-value measure left)
      (q3527166-measure-value measure right)))))

(defun-sk q3527166-measure-monotone-p
    (real group measure)
  (forall (left right)
    (implies
     (and
      (q3527166-set-p group left)
      (q3527166-set-p group right)
      (q3527166-subset-p group left right))
     (q3527166-enn-leq
      real
      (q3527166-measure-value measure left)
      (q3527166-measure-value measure right)))))

(defun-sk q3527166-measure-finite-additive-p
    (real measurable-space group measure)
  (forall (left right)
    (implies
     (and
      (q3527166-measurable-p measurable-space group left)
      (q3527166-measurable-p measurable-space group right)
      (q3527166-disjoint-p group left right))
     (equal
      (q3527166-measure-value
       measure (q3527166-union-set group left right))
      (q3527166-enn-add
       real
       (q3527166-measure-value measure left)
       (q3527166-measure-value measure right))))))

(defun q3527166-measure-partial-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q3527166-enn-zero real)
    (let ((index (1- count)))
      (q3527166-enn-add
       real
       (q3527166-measure-partial-sum
        real measure sequence index)
       (q3527166-measure-value
        measure (q3527166-sequence-set sequence index))))))

(defun-sk q3527166-set-sequence-p (group sequence)
  (forall (n)
    (implies
     (natp n)
     (q3527166-set-p
      group (q3527166-sequence-set sequence n)))))

(defun-sk q3527166-partial-sums-bounded-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q3527166-enn-leq
      real
      (q3527166-measure-partial-sum
       real measure sequence count)
      bound))))

(defun-sk q3527166-measure-countably-subadditive-p
    (real group measure)
  (forall (sequence bound)
    (implies
     (and
      (q3527166-set-sequence-p group sequence)
      (q3527166-enn-p real bound)
      (q3527166-partial-sums-bounded-p
       real measure sequence bound))
     (q3527166-enn-leq
      real
      (q3527166-measure-value
       measure (q3527166-sequence-union-set group sequence))
      bound))))

(defun-sk q3527166-sequence-measures-bounded-p
    (real measure sequence bound)
  (forall (n)
    (implies
     (natp n)
     (q3527166-enn-leq
      real
      (q3527166-measure-value
       measure (q3527166-sequence-set sequence n))
      bound))))

(defun-sk q3527166-union-measure-upper-bound-p
    (real group measure sequence)
  (forall (n)
    (implies
     (natp n)
     (q3527166-enn-leq
      real
      (q3527166-measure-value
       measure (q3527166-sequence-set sequence n))
      (q3527166-measure-value
       measure (q3527166-sequence-union-set group sequence))))))

(defun-sk q3527166-union-measure-least-upper-p
    (real group measure sequence)
  (forall (bound)
    (implies
     (and
      (q3527166-enn-p real bound)
      (q3527166-sequence-measures-bounded-p
       real measure sequence bound))
     (q3527166-enn-leq
      real
      (q3527166-measure-value
       measure (q3527166-sequence-union-set group sequence))
      bound))))

(defun-sk q3527166-measure-continuous-below-p
    (real measurable-space group measure)
  (forall (sequence)
    (implies
     (and
      (q3527166-measurable-sequence-p
       measurable-space group sequence)
      (q3527166-increasing-sequence-p group sequence))
     (and
      (q3527166-union-measure-upper-bound-p
       real group measure sequence)
      (q3527166-union-measure-least-upper-p
       real group measure sequence)))))

(defun q3527166-measure-p
    (real measurable-space group measure)
  (and
   (q3527166-measure-values-p real group measure)
   (q3527166-measure-extensional-p group measure)
   (q3527166-measure-monotone-p real group measure)
   (equal
    (q3527166-measure-value
     measure (q3527166-empty-set group))
    (q3527166-enn-zero real))
   (q3527166-measure-finite-additive-p
    real measurable-space group measure)
   (q3527166-measure-countably-subadditive-p
    real group measure)
   (q3527166-measure-continuous-below-p
    real measurable-space group measure)))

;; Left Haar and inner-regularity hypotheses.

(defun-sk q3527166-left-invariant-p
    (group measure)
  (forall (element set)
    (implies
     (and
      (q3527166-carrier-p group element)
      (q3527166-set-p group set))
     (equal
      (q3527166-measure-value
       measure
       (q3527166-left-translate-set group element set))
      (q3527166-measure-value measure set)))))

(defun-sk q3527166-finite-on-compacts-p
    (real topology group measure)
  (forall (set)
    (implies
     (and
      (q3527166-set-p group set)
      (q3527166-compact-p topology group set))
     (q3527166-enn-less
      real
      (q3527166-measure-value measure set)
      (q3527166-enn-top)))))

(defun-sk q3527166-positive-on-open-p
    (real topology group measure)
  (forall (set)
    (implies
     (and
      (q3527166-open-p topology group set)
      (q3527166-set-nonempty-p group set))
     (q3527166-enn-less
      real
      (q3527166-enn-zero real)
      (q3527166-measure-value measure set)))))

(defun q3527166-haar-measure-p
    (real topology group measure)
  (and
   (q3527166-left-invariant-p group measure)
   (q3527166-finite-on-compacts-p
    real topology group measure)
   (q3527166-positive-on-open-p
    real topology group measure)))

(defun-sk q3527166-inner-compact-approximation-p
    (real topology group measure set bound)
  (exists (compact-set)
    (and
     (q3527166-set-p group compact-set)
     (q3527166-compact-p topology group compact-set)
     (q3527166-subset-p group compact-set set)
     (q3527166-enn-less
      real bound
      (q3527166-measure-value measure compact-set)))))

(defun-sk q3527166-inner-regular-p
    (real topology measurable-space group measure)
  (forall (set bound)
    (implies
     (and
      (q3527166-measurable-p measurable-space group set)
      (q3527166-enn-p real bound)
      (q3527166-enn-less
       real bound
       (q3527166-measure-value measure set)))
     (q3527166-inner-compact-approximation-p
      real topology group measure set bound))))

;; Pointwise division E/E and membership in the identity neighborhood filter.

(defun-sk q3527166-quotient-member-p (group set x)
  (exists (left right)
    (and
     (q3527166-set-member-p group set left)
     (q3527166-set-member-p group set right)
     (equal
      x
      (q3527166-mul
       group left (q3527166-inv group right))))))

(defun-sk q3527166-subset-of-quotient-p
    (group neighborhood set)
  (forall (x)
    (implies
     (q3527166-set-member-p group neighborhood x)
     (q3527166-quotient-member-p group set x))))

(defun-sk q3527166-open-subset-of-quotient-p
    (topology group set)
  (exists (neighborhood)
    (and
     (q3527166-open-p topology group neighborhood)
     (q3527166-set-member-p
      group neighborhood (q3527166-one group))
     (q3527166-subset-of-quotient-p
      group neighborhood set))))

(defun-sk thousand-theorems-q3527166-steinhaus-theorem-statement ()
  (forall (real group topology measurable-space measure set)
    (implies
     (and
      (q3527166-real-field-p real)
      (q3527166-group-laws-p group)
      (q3527166-set-operation-laws-p group)
      (q3527166-topology-laws-p topology group)
      (q3527166-compact-extensional-p topology group)
      (q3527166-topological-group-p topology group)
      (q3527166-locally-compact-p topology group)
      (q3527166-borel-space-p
       topology measurable-space group)
      (q3527166-measure-p
       real measurable-space group measure)
      (q3527166-haar-measure-p
       real topology group measure)
      (q3527166-inner-regular-p
       real topology measurable-space group measure)
      (q3527166-set-p group set)
      (q3527166-measurable-p measurable-space group set)
      (q3527166-enn-less
       real
       (q3527166-enn-zero real)
       (q3527166-measure-value measure set)))
     (q3527166-open-subset-of-quotient-p
      topology group set))))

(value-triple :itpeval-statement-checked)
:q
