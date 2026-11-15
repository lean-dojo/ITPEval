;; Statement-only formalization of thousand-theorems corpus artifact Q939927,
;; "Stone–Weierstrass theorem": a point-separating real subalgebra of
;; continuous functions on an arbitrary compact topological space is uniformly
;; dense in all real-valued continuous functions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent arbitrary carriers, real values, sets,
;; families of sets, functions, and subalgebras.  Every ordered-field,
;; completeness, topology, compactness, continuity, and algebra law used by
;; the statement is made explicit below.

(defstub q939927-member-p (carrier object) t)
(defstub q939927-set-member-p (set-tag object) t)
(defstub q939927-family-member-p (family-tag set-tag) t)

(defstub q939927-zero (real-type) t)
(defstub q939927-one (real-type) t)
(defstub q939927-add (real-type left right) t)
(defstub q939927-multiply (real-type left right) t)
(defstub q939927-negate (real-type value) t)
(defstub q939927-inverse (real-type value) t)
(defstub q939927-less (real-type left right) t)

(defstub q939927-empty-set (carrier) t)
(defstub q939927-full-set (carrier) t)
(defstub q939927-intersection-set (carrier left right) t)
(defstub q939927-union-set (carrier family) t)

(defstub q939927-function-value (function point) t)
(defstub q939927-subalgebra-member-p (subalgebra function) t)

;; A complete ordered field presents the real scalar field without replacing
;; real values by rationals or floating-point numbers.

(defun q939927-leq (real-type left right)
  (not (q939927-less real-type right left)))

(defun q939927-subtract (real-type left right)
  (q939927-add
   real-type left (q939927-negate real-type right)))

(defun q939927-absolute (real-type value)
  (if (q939927-less
       real-type value (q939927-zero real-type))
      (q939927-negate real-type value)
    value))

(defun-sk q939927-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q939927-member-p real-type x)
      (q939927-member-p real-type y)
      (q939927-member-p real-type z))
     (let ((zero (q939927-zero real-type))
           (one (q939927-one real-type)))
       (and
        (q939927-member-p
         real-type (q939927-add real-type x y))
        (q939927-member-p
         real-type (q939927-multiply real-type x y))
        (q939927-member-p
         real-type (q939927-negate real-type x))
        (q939927-member-p
         real-type (q939927-inverse real-type x))
        (equal
         (q939927-add
          real-type (q939927-add real-type x y) z)
         (q939927-add
          real-type x (q939927-add real-type y z)))
        (equal
         (q939927-add real-type x y)
         (q939927-add real-type y x))
        (equal (q939927-add real-type x zero) x)
        (equal
         (q939927-add
          real-type x (q939927-negate real-type x))
         zero)
        (equal
         (q939927-multiply
          real-type (q939927-multiply real-type x y) z)
         (q939927-multiply
          real-type x (q939927-multiply real-type y z)))
        (equal
         (q939927-multiply real-type x y)
         (q939927-multiply real-type y x))
        (equal (q939927-multiply real-type x one) x)
        (equal
         (q939927-multiply real-type x zero)
         zero)
        (equal
         (q939927-inverse real-type zero)
         zero)
        (implies
         (not (equal x zero))
         (equal
          (q939927-multiply
           real-type x (q939927-inverse real-type x))
          one))
        (equal
         (q939927-multiply
          real-type x (q939927-add real-type y z))
         (q939927-add
          real-type
          (q939927-multiply real-type x y)
          (q939927-multiply real-type x z))))))))

(defun-sk q939927-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q939927-member-p real-type x)
      (q939927-member-p real-type y)
      (q939927-member-p real-type z))
     (let ((zero (q939927-zero real-type)))
       (and
        (not (q939927-less real-type x x))
        (or
         (equal x y)
         (q939927-less real-type x y)
         (q939927-less real-type y x))
        (implies
         (and
          (q939927-less real-type x y)
          (q939927-less real-type y z))
         (q939927-less real-type x z))
        (implies
         (q939927-less real-type x y)
         (q939927-less
          real-type
          (q939927-add real-type x z)
          (q939927-add real-type y z)))
        (implies
         (and
          (q939927-less real-type zero x)
          (q939927-less real-type zero y))
         (q939927-less
          real-type
          zero
          (q939927-multiply real-type x y))))))))

(defun-sk q939927-real-set-nonempty-p
    (real-type set-tag)
  (exists (x)
    (and
     (q939927-member-p real-type x)
     (q939927-set-member-p set-tag x))))

(defun-sk q939927-real-upper-bound-p
    (real-type set-tag bound)
  (forall (x)
    (implies
     (and
      (q939927-member-p real-type x)
      (q939927-set-member-p set-tag x))
     (q939927-leq real-type x bound))))

(defun-sk q939927-real-set-bounded-above-p
    (real-type set-tag)
  (exists (bound)
    (and
     (q939927-member-p real-type bound)
     (q939927-real-upper-bound-p
      real-type set-tag bound))))

(defun-sk q939927-least-upper-bound-p
    (real-type set-tag supremum)
  (forall (bound)
    (and
     (q939927-member-p real-type supremum)
     (q939927-real-upper-bound-p
      real-type set-tag supremum)
     (implies
      (and
       (q939927-member-p real-type bound)
       (q939927-real-upper-bound-p
        real-type set-tag bound))
      (q939927-leq real-type supremum bound)))))

(defun-sk q939927-least-upper-bound-exists-p
    (real-type set-tag)
  (exists (supremum)
    (q939927-least-upper-bound-p
     real-type set-tag supremum)))

(defun-sk q939927-dedekind-complete-p (real-type)
  (forall (set-tag)
    (implies
     (and
      (q939927-real-set-nonempty-p real-type set-tag)
      (q939927-real-set-bounded-above-p
       real-type set-tag))
     (q939927-least-upper-bound-exists-p
      real-type set-tag))))

(defun q939927-real-field-p (real-type)
  (and
   (q939927-member-p
    real-type (q939927-zero real-type))
   (q939927-member-p
    real-type (q939927-one real-type))
   (not
    (equal
     (q939927-zero real-type)
     (q939927-one real-type)))
   (q939927-field-laws-p real-type)
   (q939927-order-laws-p real-type)
   (q939927-less
    real-type
    (q939927-zero real-type)
    (q939927-one real-type))
   (q939927-dedekind-complete-p real-type)))

;; Sets and arbitrary families of sets present the topology on the source.

(defun-sk q939927-set-contained-p (carrier set-tag)
  (forall (x)
    (implies
     (q939927-set-member-p set-tag x)
     (q939927-member-p carrier x))))

(defun q939927-valid-set-p (carrier set-tag)
  (q939927-set-contained-p carrier set-tag))

(defun-sk q939927-set-equivalent-p
    (carrier left right)
  (forall (x)
    (implies
     (q939927-member-p carrier x)
     (iff
      (q939927-set-member-p left x)
      (q939927-set-member-p right x)))))

(defun-sk q939927-family-members-valid-p
    (carrier family)
  (forall (set-tag)
    (implies
     (q939927-family-member-p family set-tag)
     (q939927-valid-set-p carrier set-tag))))

(defun q939927-open-set-p
    (carrier topology set-tag)
  (and
   (q939927-valid-set-p carrier set-tag)
   (q939927-family-member-p topology set-tag)))

(defun-sk q939927-topology-extensional-p
    (carrier topology)
  (forall (left right)
    (implies
     (and
      (q939927-valid-set-p carrier left)
      (q939927-valid-set-p carrier right)
      (q939927-set-equivalent-p carrier left right))
     (iff
      (q939927-family-member-p topology left)
      (q939927-family-member-p topology right)))))

(defun-sk q939927-empty-set-law-p (carrier)
  (forall (x)
    (implies
     (q939927-member-p carrier x)
     (not
      (q939927-set-member-p
       (q939927-empty-set carrier) x)))))

(defun-sk q939927-full-set-law-p (carrier)
  (forall (x)
    (implies
     (q939927-member-p carrier x)
     (q939927-set-member-p
      (q939927-full-set carrier) x))))

(defun-sk q939927-intersection-set-law-p
    (carrier left right)
  (forall (x)
    (implies
     (q939927-member-p carrier x)
     (iff
      (q939927-set-member-p
       (q939927-intersection-set
        carrier left right)
       x)
      (and
       (q939927-set-member-p left x)
       (q939927-set-member-p right x))))))

(defun-sk q939927-union-member-p
    (carrier family x)
  (exists (set-tag)
    (and
     (q939927-valid-set-p carrier set-tag)
     (q939927-family-member-p family set-tag)
     (q939927-set-member-p set-tag x))))

(defun-sk q939927-union-set-law-p
    (carrier family)
  (forall (x)
    (implies
     (q939927-member-p carrier x)
     (iff
      (q939927-set-member-p
       (q939927-union-set carrier family) x)
      (q939927-union-member-p
       carrier family x)))))

(defun-sk q939927-family-members-open-p
    (carrier topology family)
  (forall (set-tag)
    (implies
     (q939927-family-member-p family set-tag)
     (q939927-open-set-p
      carrier topology set-tag))))

(defun-sk q939927-topology-closure-laws-p
    (carrier topology)
  (forall (left right family)
    (and
     (implies
      (and
       (q939927-open-set-p carrier topology left)
       (q939927-open-set-p carrier topology right))
      (and
       (q939927-intersection-set-law-p
        carrier left right)
       (q939927-open-set-p
        carrier topology
        (q939927-intersection-set
         carrier left right))))
     (implies
      (and
       (q939927-family-members-valid-p
        carrier family)
       (q939927-family-members-open-p
        carrier topology family))
      (and
       (q939927-union-set-law-p carrier family)
       (q939927-open-set-p
        carrier topology
        (q939927-union-set carrier family)))))))

(defun q939927-topological-space-p
    (carrier topology)
  (and
   (q939927-family-members-valid-p carrier topology)
   (q939927-topology-extensional-p carrier topology)
   (q939927-valid-set-p
    carrier (q939927-empty-set carrier))
   (q939927-valid-set-p
    carrier (q939927-full-set carrier))
   (q939927-empty-set-law-p carrier)
   (q939927-full-set-law-p carrier)
   (q939927-open-set-p
    carrier topology (q939927-empty-set carrier))
   (q939927-open-set-p
    carrier topology (q939927-full-set carrier))
   (q939927-topology-closure-laws-p
    carrier topology)))

;; Compactness quantifies over unrestricted open-cover families and keeps the
;; finite-subcover witness inside the compactness predicate.

(defun-sk q939927-cover-point-p
    (carrier family point)
  (exists (set-tag)
    (and
     (q939927-valid-set-p carrier set-tag)
     (q939927-family-member-p family set-tag)
     (q939927-set-member-p set-tag point))))

(defun-sk q939927-open-cover-p
    (carrier topology family)
  (forall (object)
    (and
     (implies
      (q939927-family-member-p family object)
      (q939927-open-set-p
       carrier topology object))
     (implies
      (q939927-member-p carrier object)
      (q939927-cover-point-p
       carrier family object)))))

(defun q939927-finite-subcover-elements-p
    (sets family)
  (if (consp sets)
      (and
       (q939927-family-member-p family (car sets))
       (q939927-finite-subcover-elements-p
        (cdr sets) family))
    (equal sets nil)))

(defun q939927-finite-subcover-point-p
    (sets point)
  (if (consp sets)
      (or
       (q939927-set-member-p (car sets) point)
       (q939927-finite-subcover-point-p
        (cdr sets) point))
    nil))

(defun-sk q939927-finite-subcover-covers-p
    (carrier sets)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (q939927-finite-subcover-point-p
      sets point))))

(defun q939927-finite-subcover-p
    (carrier family sets)
  (and
   (true-listp sets)
   (q939927-finite-subcover-elements-p
    sets family)
   (q939927-finite-subcover-covers-p
    carrier sets)))

(defun-sk q939927-finite-subcover-exists-p
    (carrier family)
  (exists (sets)
    (q939927-finite-subcover-p
     carrier family sets)))

(defun-sk q939927-compactness-law-p
    (carrier topology)
  (forall (family)
    (implies
     (q939927-open-cover-p
      carrier topology family)
     (q939927-finite-subcover-exists-p
      carrier family))))

(defun q939927-compact-topological-space-p
    (carrier topology)
  (and
   (q939927-topological-space-p carrier topology)
   (q939927-compactness-law-p carrier topology)))

;; Continuity uses the neighborhood characterization for maps into the real
;; metric topology.  It is equivalent to inverse-image continuity.

(defun-sk q939927-function-typed-p
    (carrier real-type function)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (q939927-member-p
      real-type
      (q939927-function-value function point)))))

(defun q939927-positive-real-p
    (real-type value)
  (and
   (q939927-member-p real-type value)
   (q939927-less
    real-type (q939927-zero real-type) value)))

(defun q939927-values-close-p
    (real-type left right epsilon)
  (q939927-less
   real-type
   (q939927-absolute
    real-type
    (q939927-subtract real-type left right))
   epsilon))

(defun-sk q939927-neighborhood-controls-function-p
    (carrier real-type topology function
     center epsilon neighborhood)
  (forall (point)
    (and
     (q939927-open-set-p
      carrier topology neighborhood)
     (q939927-set-member-p neighborhood center)
     (implies
      (and
       (q939927-member-p carrier point)
       (q939927-set-member-p neighborhood point))
      (q939927-values-close-p
       real-type
       (q939927-function-value function point)
       (q939927-function-value function center)
       epsilon)))))

(defun-sk q939927-continuity-neighborhood-exists-p
    (carrier real-type topology function
     center epsilon)
  (exists (neighborhood)
    (q939927-neighborhood-controls-function-p
     carrier real-type topology function
     center epsilon neighborhood)))

(defun-sk q939927-continuity-law-p
    (carrier real-type topology function)
  (forall (center epsilon)
    (implies
     (and
      (q939927-member-p carrier center)
      (q939927-positive-real-p
       real-type epsilon))
     (q939927-continuity-neighborhood-exists-p
      carrier real-type topology function
      center epsilon))))

(defun q939927-continuous-real-map-p
    (carrier real-type topology function)
  (and
   (q939927-function-typed-p
    carrier real-type function)
   (q939927-continuity-law-p
    carrier real-type topology function)))

;; Pointwise equality and operations make the bundled real subalgebra
;; structure explicit while leaving all function witnesses existential.

(defun-sk q939927-functions-equal-p
    (carrier left right)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (equal
      (q939927-function-value left point)
      (q939927-function-value right point)))))

(defun-sk q939927-constant-function-p
    (carrier function constant)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (equal
      (q939927-function-value function point)
      constant))))

(defun-sk q939927-pointwise-add-p
    (carrier real-type left right sum)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (equal
      (q939927-function-value sum point)
      (q939927-add
       real-type
       (q939927-function-value left point)
       (q939927-function-value right point))))))

(defun-sk q939927-pointwise-multiply-p
    (carrier real-type left right product)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (equal
      (q939927-function-value product point)
      (q939927-multiply
       real-type
       (q939927-function-value left point)
       (q939927-function-value right point))))))

(defun-sk q939927-pointwise-negate-p
    (carrier real-type function negative)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (equal
      (q939927-function-value negative point)
      (q939927-negate
       real-type
       (q939927-function-value function point))))))

(defun-sk q939927-subalgebra-extensional-p
    (carrier real-type subalgebra)
  (forall (left right)
    (implies
     (and
      (q939927-function-typed-p
       carrier real-type left)
      (q939927-function-typed-p
       carrier real-type right)
      (q939927-functions-equal-p
       carrier left right))
     (iff
      (q939927-subalgebra-member-p
       subalgebra left)
      (q939927-subalgebra-member-p
       subalgebra right)))))

(defun-sk q939927-subalgebra-members-continuous-p
    (carrier real-type topology subalgebra)
  (forall (function)
    (implies
     (q939927-subalgebra-member-p
      subalgebra function)
     (q939927-continuous-real-map-p
      carrier real-type topology function))))

(defun-sk q939927-constant-member-exists-p
    (carrier real-type subalgebra constant)
  (exists (function)
    (and
     (q939927-subalgebra-member-p
      subalgebra function)
     (q939927-constant-function-p
      carrier function constant))))

(defun-sk q939927-all-constants-member-p
    (carrier real-type subalgebra)
  (forall (constant)
    (implies
     (q939927-member-p real-type constant)
     (q939927-constant-member-exists-p
      carrier real-type subalgebra constant))))

(defun-sk q939927-sum-member-exists-p
    (carrier real-type subalgebra left right)
  (exists (sum)
    (and
     (q939927-subalgebra-member-p subalgebra sum)
     (q939927-pointwise-add-p
      carrier real-type left right sum))))

(defun-sk q939927-product-member-exists-p
    (carrier real-type subalgebra left right)
  (exists (product)
    (and
     (q939927-subalgebra-member-p
      subalgebra product)
     (q939927-pointwise-multiply-p
      carrier real-type left right product))))

(defun-sk q939927-negative-member-exists-p
    (carrier real-type subalgebra function)
  (exists (negative)
    (and
     (q939927-subalgebra-member-p
      subalgebra negative)
     (q939927-pointwise-negate-p
      carrier real-type function negative))))

(defun-sk q939927-subalgebra-operation-laws-p
    (carrier real-type subalgebra)
  (forall (left right)
    (and
     (implies
      (q939927-subalgebra-member-p
       subalgebra left)
      (q939927-negative-member-exists-p
       carrier real-type subalgebra left))
     (implies
      (and
       (q939927-subalgebra-member-p
        subalgebra left)
       (q939927-subalgebra-member-p
        subalgebra right))
      (and
       (q939927-sum-member-exists-p
        carrier real-type subalgebra left right)
       (q939927-product-member-exists-p
        carrier real-type subalgebra left right))))))

(defun q939927-real-subalgebra-p
    (carrier real-type topology subalgebra)
  (and
   (q939927-subalgebra-extensional-p
    carrier real-type subalgebra)
   (q939927-subalgebra-members-continuous-p
    carrier real-type topology subalgebra)
   (q939927-all-constants-member-p
    carrier real-type subalgebra)
   (q939927-subalgebra-operation-laws-p
    carrier real-type subalgebra)))

;; The point-separation hypothesis and the equivalent positive-epsilon
;; characterization of topological closure being the whole function algebra.

(defun-sk q939927-separating-function-exists-p
    (subalgebra left-point right-point)
  (exists (function)
    (and
     (q939927-subalgebra-member-p
      subalgebra function)
     (not
      (equal
       (q939927-function-value
        function left-point)
       (q939927-function-value
        function right-point))))))

(defun-sk q939927-separates-points-p
    (carrier subalgebra)
  (forall (left-point right-point)
    (implies
     (and
      (q939927-member-p carrier left-point)
      (q939927-member-p carrier right-point)
      (not (equal left-point right-point)))
     (q939927-separating-function-exists-p
      subalgebra left-point right-point))))

(defun-sk q939927-uniformly-close-p
    (carrier real-type left right epsilon)
  (forall (point)
    (implies
     (q939927-member-p carrier point)
     (q939927-values-close-p
      real-type
      (q939927-function-value left point)
      (q939927-function-value right point)
      epsilon))))

(defun-sk q939927-approximant-exists-p
    (carrier real-type subalgebra function epsilon)
  (exists (approximant)
    (and
     (q939927-subalgebra-member-p
      subalgebra approximant)
     (q939927-uniformly-close-p
      carrier real-type approximant function epsilon))))

(defun-sk q939927-uniformly-dense-p
    (carrier real-type topology subalgebra)
  (forall (function epsilon)
    (implies
     (and
      (q939927-continuous-real-map-p
       carrier real-type topology function)
      (q939927-positive-real-p
       real-type epsilon))
     (q939927-approximant-exists-p
      carrier real-type subalgebra
      function epsilon))))

(defun-sk
    thousand-theorems-q939927-stone-weierstrass-theorem-statement ()
  (forall (real-type carrier topology subalgebra)
    (implies
     (and
      (q939927-real-field-p real-type)
      (q939927-compact-topological-space-p
       carrier topology)
      (q939927-real-subalgebra-p
       carrier real-type topology subalgebra)
      (q939927-separates-points-p
       carrier subalgebra))
     (q939927-uniformly-dense-p
      carrier real-type topology subalgebra))))

(value-triple :itpeval-statement-checked)
:q
