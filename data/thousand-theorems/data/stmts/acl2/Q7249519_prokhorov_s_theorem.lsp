;; Statement-only formalization of thousand-theorems corpus artifact Q7249519,
;; "Prokhorov's theorem": on an arbitrary Hausdorff Borel space, finite
;; measures with uniformly bounded mass and uniformly vanishing tails outside
;; compact sets form a compact set in the weak topology, under normality or a
;; monotone compact exhaustion. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The conservative interfaces below range over arbitrary carriers, sets,
;; families, functions, sequences, and measures.  Their explicit laws present
;; the complete ordered real field, topology, Borel sigma algebra, finite
;; measures, exact bounded Lebesgue integration, and the generated weak
;; topology used in the source statement.  No carrier, set, function, cover,
;; or measure family is restricted to a finite table.

(defstub q7249519-member-p (type object) t)
(defstub q7249519-set-member-p (set object) t)
(defstub q7249519-family-member-p (family set) t)
(defstub q7249519-function-at (function argument) t)
(defstub q7249519-sequence-at (sequence index) t)

(defstub q7249519-zero (real) t)
(defstub q7249519-one (real) t)
(defstub q7249519-add (real left right) t)
(defstub q7249519-multiply (real left right) t)
(defstub q7249519-negate (real value) t)
(defstub q7249519-inverse (real value) t)
(defstub q7249519-less (real left right) t)

(defstub q7249519-empty-set (type) t)
(defstub q7249519-full-set (type) t)
(defstub q7249519-complement-set (type set) t)
(defstub q7249519-intersection-set (type left right) t)
(defstub q7249519-union-set (type family) t)
(defstub q7249519-countable-union-set (type sequence) t)
(defstub q7249519-preimage-set (domain function codomain-set) t)
(defstub q7249519-fiber-set (domain function value) t)

(defstub q7249519-measure-value (measure set) t)
(defstub q7249519-lintegral-value (measure function) t)
(defstub q7249519-positive-part-function (real function) t)
(defstub q7249519-negative-part-function (real function) t)

(defstub q7249519-finite-measure-type (real space measurable) t)
(defstub q7249519-integral-preimage-set
  (real space topology measurable function real-open-set) t)
(defstub q7249519-prokhorov-target-set
  (real space measurable u compact-sequence mass-bound) t)

(defun q7249519-leq (real left right)
  (not (q7249519-less real right left)))

(defun q7249519-positive-p (real value)
  (and
   (q7249519-member-p real value)
   (q7249519-less real (q7249519-zero real) value)))

(defun q7249519-nonnegative-p (real value)
  (and
   (q7249519-member-p real value)
   (q7249519-leq real (q7249519-zero real) value)))

(defun q7249519-subtract (real left right)
  (q7249519-add real left (q7249519-negate real right)))

(defun q7249519-absolute-value (real value)
  (if (q7249519-less real value (q7249519-zero real))
      (q7249519-negate real value)
    value))

;; A Dedekind-complete ordered field presents the real numbers.

(defun-sk q7249519-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q7249519-member-p real x)
      (q7249519-member-p real y)
      (q7249519-member-p real z))
     (let ((zero (q7249519-zero real))
           (one (q7249519-one real)))
       (and
        (q7249519-member-p real (q7249519-add real x y))
        (q7249519-member-p real (q7249519-multiply real x y))
        (q7249519-member-p real (q7249519-negate real x))
        (q7249519-member-p real (q7249519-inverse real x))
        (equal
         (q7249519-add real (q7249519-add real x y) z)
         (q7249519-add real x (q7249519-add real y z)))
        (equal (q7249519-add real x y)
               (q7249519-add real y x))
        (equal (q7249519-add real x zero) x)
        (equal
         (q7249519-add real x (q7249519-negate real x))
         zero)
        (equal
         (q7249519-multiply
          real (q7249519-multiply real x y) z)
         (q7249519-multiply
          real x (q7249519-multiply real y z)))
        (equal (q7249519-multiply real x y)
               (q7249519-multiply real y x))
        (equal (q7249519-multiply real x one) x)
        (implies
         (not (equal x zero))
         (equal
          (q7249519-multiply
           real x (q7249519-inverse real x))
          one))
        (equal
         (q7249519-multiply
          real x (q7249519-add real y z))
         (q7249519-add
          real
          (q7249519-multiply real x y)
          (q7249519-multiply real x z))))))))

(defun-sk q7249519-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q7249519-member-p real x)
      (q7249519-member-p real y)
      (q7249519-member-p real z))
     (and
      (not (q7249519-less real x x))
      (or (equal x y)
          (q7249519-less real x y)
          (q7249519-less real y x))
      (implies
       (and
        (q7249519-less real x y)
        (q7249519-less real y z))
       (q7249519-less real x z))
      (implies
       (q7249519-less real x y)
       (q7249519-less
        real
        (q7249519-add real x z)
        (q7249519-add real y z)))
      (implies
       (and
        (q7249519-less real (q7249519-zero real) x)
        (q7249519-less real (q7249519-zero real) y))
       (q7249519-less
        real
        (q7249519-zero real)
        (q7249519-multiply real x y)))))))

(defun-sk q7249519-real-set-nonempty-p (real set)
  (exists (value)
    (and
     (q7249519-member-p real value)
     (q7249519-set-member-p set value))))

(defun-sk q7249519-upper-bound-p (real set bound)
  (forall (value)
    (implies
     (and
      (q7249519-member-p real value)
      (q7249519-set-member-p set value))
     (q7249519-leq real value bound))))

(defun-sk q7249519-bounded-above-p (real set)
  (exists (bound)
    (and
     (q7249519-member-p real bound)
     (q7249519-upper-bound-p real set bound))))

(defun-sk q7249519-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q7249519-member-p real supremum)
     (q7249519-upper-bound-p real set supremum)
     (implies
      (and
       (q7249519-member-p real bound)
       (q7249519-upper-bound-p real set bound))
      (q7249519-leq real supremum bound)))))

(defun-sk q7249519-supremum-exists-p (real set)
  (exists (supremum)
    (q7249519-supremum-p real set supremum)))

(defun-sk q7249519-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q7249519-real-set-nonempty-p real set)
      (q7249519-bounded-above-p real set))
     (q7249519-supremum-exists-p real set))))

(defun q7249519-real-structure-p (real)
  (and
   (q7249519-member-p real (q7249519-zero real))
   (q7249519-member-p real (q7249519-one real))
   (not (equal (q7249519-zero real)
               (q7249519-one real)))
   (q7249519-field-laws-p real)
   (q7249519-order-laws-p real)
   (q7249519-less
    real (q7249519-zero real) (q7249519-one real))
   (q7249519-dedekind-complete-p real)))

;; Arbitrary sets, set families, and their extensional constructors.

(defun-sk q7249519-valid-set-p (type set)
  (forall (object)
    (implies
     (q7249519-set-member-p set object)
     (q7249519-member-p type object))))

(defun-sk q7249519-set-equiv-p (type left right)
  (forall (object)
    (implies
     (q7249519-member-p type object)
     (iff
      (q7249519-set-member-p left object)
      (q7249519-set-member-p right object)))))

(defun-sk q7249519-set-subset-p (type left right)
  (forall (object)
    (implies
     (and
      (q7249519-member-p type object)
      (q7249519-set-member-p left object))
     (q7249519-set-member-p right object))))

(defun-sk q7249519-family-valid-p (type family)
  (forall (set)
    (implies
     (q7249519-family-member-p family set)
     (q7249519-valid-set-p type set))))

(defun-sk q7249519-family-extensional-p (type family)
  (forall (left right)
    (implies
     (and
      (q7249519-valid-set-p type left)
      (q7249519-valid-set-p type right)
      (q7249519-set-equiv-p type left right))
     (iff
      (q7249519-family-member-p family left)
      (q7249519-family-member-p family right)))))

(defun q7249519-family-of-sets-p (type family)
  (and
   (q7249519-family-valid-p type family)
   (q7249519-family-extensional-p type family)))

(defun-sk q7249519-union-member-p (family object)
  (exists (set)
    (and
     (q7249519-family-member-p family set)
     (q7249519-set-member-p set object))))

(defun-sk q7249519-countable-union-member-p (sequence object)
  (exists (index)
    (and
     (natp index)
     (q7249519-set-member-p
      (q7249519-sequence-at sequence index)
      object))))

(defun-sk q7249519-set-constructor-laws-p (type)
  (forall (object left right family sequence function codomain-set value)
    (implies
     (q7249519-member-p type object)
     (and
      (not
       (q7249519-set-member-p
        (q7249519-empty-set type) object))
      (q7249519-set-member-p
       (q7249519-full-set type) object)
      (iff
       (q7249519-set-member-p
        (q7249519-complement-set type left) object)
       (not (q7249519-set-member-p left object)))
      (iff
       (q7249519-set-member-p
        (q7249519-intersection-set type left right)
        object)
       (and
        (q7249519-set-member-p left object)
        (q7249519-set-member-p right object)))
      (iff
       (q7249519-set-member-p
        (q7249519-union-set type family) object)
       (q7249519-union-member-p family object))
      (iff
       (q7249519-set-member-p
        (q7249519-countable-union-set type sequence)
        object)
       (q7249519-countable-union-member-p sequence object))
      (iff
       (q7249519-set-member-p
        (q7249519-preimage-set
         type function codomain-set)
        object)
       (q7249519-set-member-p
        codomain-set
        (q7249519-function-at function object)))
      (iff
       (q7249519-set-member-p
        (q7249519-fiber-set type function value)
        object)
       (equal
        (q7249519-function-at function object)
        value))))))

;; Topological spaces, compact sets, Hausdorffness, and normality.

(defun q7249519-open-set-p (type topology set)
  (and
   (q7249519-valid-set-p type set)
   (q7249519-family-member-p topology set)))

(defun-sk q7249519-open-family-p (type topology family)
  (forall (set)
    (implies
     (q7249519-family-member-p family set)
     (q7249519-open-set-p type topology set))))

(defun-sk q7249519-topology-intersections-p (type topology)
  (forall (left right)
    (implies
     (and
      (q7249519-open-set-p type topology left)
      (q7249519-open-set-p type topology right))
     (q7249519-open-set-p
      type topology
      (q7249519-intersection-set type left right)))))

(defun-sk q7249519-topology-unions-p (type topology)
  (forall (family)
    (implies
     (and
      (q7249519-family-of-sets-p type family)
      (q7249519-open-family-p type topology family))
     (q7249519-open-set-p
      type topology
      (q7249519-union-set type family)))))

(defun q7249519-topological-space-p (type topology)
  (and
   (q7249519-family-of-sets-p type topology)
   (q7249519-open-set-p
    type topology (q7249519-empty-set type))
   (q7249519-open-set-p
    type topology (q7249519-full-set type))
   (q7249519-topology-intersections-p type topology)
   (q7249519-topology-unions-p type topology)))

(defun q7249519-closed-set-p (type topology set)
  (and
   (q7249519-valid-set-p type set)
   (q7249519-open-set-p
    type topology
    (q7249519-complement-set type set))))

(defun-sk q7249519-disjoint-sets-p (type left right)
  (forall (object)
    (implies
     (q7249519-member-p type object)
     (not
      (and
       (q7249519-set-member-p left object)
       (q7249519-set-member-p right object))))))

(defun-sk q7249519-cover-point-p (cover object)
  (exists (set)
    (and
     (q7249519-family-member-p cover set)
     (q7249519-set-member-p set object))))

(defun-sk q7249519-cover-p (type topology target cover)
  (forall (object)
    (and
     (q7249519-valid-set-p type target)
     (q7249519-family-of-sets-p type cover)
     (q7249519-open-family-p type topology cover)
     (implies
      (and
       (q7249519-member-p type object)
       (q7249519-set-member-p target object))
      (q7249519-cover-point-p cover object)))))

(defun q7249519-finite-subcover-elements-p
    (sets type cover)
  (if (consp sets)
      (and
       (q7249519-valid-set-p type (car sets))
       (q7249519-family-member-p cover (car sets))
       (q7249519-finite-subcover-elements-p
        (cdr sets) type cover))
    (equal sets nil)))

(defun q7249519-finite-subcover-point-p (sets object)
  (if (consp sets)
      (or
       (q7249519-set-member-p (car sets) object)
       (q7249519-finite-subcover-point-p
        (cdr sets) object))
    nil))

(defun-sk q7249519-finite-subcover-covers-p
    (sets type target)
  (forall (object)
    (implies
     (and
      (q7249519-member-p type object)
      (q7249519-set-member-p target object))
     (q7249519-finite-subcover-point-p sets object))))

(defun q7249519-finite-subcover-p
    (sets type target cover)
  (and
   (true-listp sets)
   (q7249519-finite-subcover-elements-p
    sets type cover)
   (q7249519-finite-subcover-covers-p
    sets type target)))

(defun-sk q7249519-finite-subcover-exists-p
    (type target cover)
  (exists (sets)
    (q7249519-finite-subcover-p
     sets type target cover)))

(defun-sk q7249519-compact-set-p
    (type topology target)
  (forall (cover)
    (and
     (q7249519-valid-set-p type target)
     (implies
      (q7249519-cover-p type topology target cover)
      (q7249519-finite-subcover-exists-p
       type target cover)))))

(defun-sk q7249519-t2-separation-exists-p
    (type topology x y)
  (exists (left right)
    (and
     (q7249519-open-set-p type topology left)
     (q7249519-open-set-p type topology right)
     (q7249519-set-member-p left x)
     (q7249519-set-member-p right y)
     (q7249519-disjoint-sets-p type left right))))

(defun-sk q7249519-t2-space-p (type topology)
  (forall (x y)
    (implies
     (and
      (q7249519-member-p type x)
      (q7249519-member-p type y)
      (not (equal x y)))
     (q7249519-t2-separation-exists-p
      type topology x y))))

(defun-sk q7249519-normal-separation-exists-p
    (type topology left right)
  (exists (left-open right-open)
    (and
     (q7249519-open-set-p type topology left-open)
     (q7249519-open-set-p type topology right-open)
     (q7249519-set-subset-p type left left-open)
     (q7249519-set-subset-p type right right-open)
     (q7249519-disjoint-sets-p
      type left-open right-open))))

(defun-sk q7249519-normal-space-p (type topology)
  (forall (left right)
    (implies
     (and
      (q7249519-closed-set-p type topology left)
      (q7249519-closed-set-p type topology right)
      (q7249519-disjoint-sets-p type left right))
     (q7249519-normal-separation-exists-p
      type topology left right))))

;; Sigma algebras and equality with the Borel sigma algebra generated by the
;; given topology.

(defun-sk q7249519-set-sequence-p (type sequence)
  (forall (index)
    (implies
     (natp index)
     (q7249519-valid-set-p
      type (q7249519-sequence-at sequence index)))))

(defun-sk q7249519-measurable-sequence-p
    (type measurable sequence)
  (forall (index)
    (implies
     (natp index)
     (q7249519-family-member-p
      measurable
      (q7249519-sequence-at sequence index)))))

(defun-sk q7249519-sigma-complements-p
    (type measurable)
  (forall (set)
    (implies
     (q7249519-family-member-p measurable set)
     (q7249519-family-member-p
      measurable
      (q7249519-complement-set type set)))))

(defun-sk q7249519-sigma-countable-unions-p
    (type measurable)
  (forall (sequence)
    (implies
     (and
      (q7249519-set-sequence-p type sequence)
      (q7249519-measurable-sequence-p
       type measurable sequence))
     (q7249519-family-member-p
      measurable
      (q7249519-countable-union-set
       type sequence)))))

(defun q7249519-sigma-algebra-p (type measurable)
  (and
   (q7249519-family-of-sets-p type measurable)
   (q7249519-family-member-p
    measurable (q7249519-empty-set type))
   (q7249519-sigma-complements-p type measurable)
   (q7249519-sigma-countable-unions-p
    type measurable)))

(defun-sk q7249519-family-subset-p (left right)
  (forall (set)
    (implies
     (q7249519-family-member-p left set)
     (q7249519-family-member-p right set))))

(defun-sk q7249519-borel-minimal-p
    (type topology measurable)
  (forall (candidate)
    (implies
     (and
      (q7249519-sigma-algebra-p type candidate)
      (q7249519-family-subset-p topology candidate))
     (q7249519-family-subset-p
      measurable candidate))))

(defun q7249519-borel-space-p
    (type topology measurable)
  (and
   (q7249519-sigma-algebra-p type measurable)
   (q7249519-family-subset-p topology measurable)
   (q7249519-borel-minimal-p
    type topology measurable)))

;; Nonnegative-real sequences and convergence to zero.

(defun-sk q7249519-nnreal-sequence-p (real sequence)
  (forall (index)
    (implies
     (natp index)
     (q7249519-nonnegative-p
      real
      (q7249519-sequence-at sequence index)))))

(defun-sk q7249519-zero-limit-tail-p
    (real sequence epsilon start)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp start)
      (<= start index))
     (q7249519-less
      real
      (q7249519-sequence-at sequence index)
      epsilon))))

(defun-sk q7249519-zero-limit-start-p
    (real sequence epsilon)
  (exists (start)
    (and
     (natp start)
     (q7249519-zero-limit-tail-p
      real sequence epsilon start))))

(defun-sk q7249519-tends-to-zero-p (real sequence)
  (forall (epsilon)
    (implies
     (q7249519-positive-p real epsilon)
     (q7249519-zero-limit-start-p
      real sequence epsilon))))

;; Countably additive finite measures with values in the nonnegative reals.

(defun-sk q7249519-pairwise-disjoint-p
    (type sequence)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (not (equal left-index right-index)))
     (q7249519-disjoint-sets-p
      type
      (q7249519-sequence-at sequence left-index)
      (q7249519-sequence-at sequence right-index)))))

(defun q7249519-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q7249519-zero real)
    (let ((index (- count 1)))
      (q7249519-add
       real
       (q7249519-measure-prefix-sum
        real measure sequence index)
       (q7249519-measure-value
        measure
        (q7249519-sequence-at sequence index))))))

(defun-sk q7249519-series-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q7249519-leq
      real
      (q7249519-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q7249519-series-sum-p
    (real measure sequence sum)
  (forall (bound)
    (and
     (q7249519-member-p real sum)
     (q7249519-series-upper-bound-p
      real measure sequence sum)
     (implies
      (and
       (q7249519-member-p real bound)
       (q7249519-series-upper-bound-p
        real measure sequence bound))
      (q7249519-leq real sum bound)))))

(defun-sk q7249519-measure-extensional-p
    (space measurable measure)
  (forall (left right)
    (implies
     (and
      (q7249519-family-member-p measurable left)
      (q7249519-family-member-p measurable right)
      (q7249519-set-equiv-p space left right))
     (equal
      (q7249519-measure-value measure left)
      (q7249519-measure-value measure right)))))

(defun-sk q7249519-measure-values-p
    (real measurable measure)
  (forall (set)
    (implies
     (q7249519-family-member-p measurable set)
     (q7249519-nonnegative-p
      real
      (q7249519-measure-value measure set)))))

(defun-sk q7249519-countable-additivity-p
    (real space measurable measure)
  (forall (sequence)
    (implies
     (and
      (q7249519-set-sequence-p space sequence)
      (q7249519-measurable-sequence-p
       space measurable sequence)
      (q7249519-pairwise-disjoint-p space sequence))
     (q7249519-series-sum-p
      real measure sequence
      (q7249519-measure-value
       measure
       (q7249519-countable-union-set
        space sequence))))))

(defun q7249519-finite-measure-p
    (real space measurable measure)
  (and
   (q7249519-measure-extensional-p
    space measurable measure)
   (q7249519-measure-values-p
    real measurable measure)
   (equal
    (q7249519-measure-value
     measure (q7249519-empty-set space))
    (q7249519-zero real))
   (q7249519-countable-additivity-p
    real space measurable measure)))

(defun-sk q7249519-finite-measure-carrier-laws-p
    (real space measurable)
  (forall (measure)
    (iff
     (q7249519-member-p
      (q7249519-finite-measure-type
       real space measurable)
      measure)
     (q7249519-finite-measure-p
      real space measurable measure))))

;; Real-valued functions, continuity, boundedness, and exact bounded Lebesgue
;; integration by suprema of measurable finite-range simple functions.

(defun-sk q7249519-real-function-p
    (real space function)
  (forall (object)
    (implies
     (q7249519-member-p space object)
     (q7249519-member-p
      real
      (q7249519-function-at function object)))))

(defun-sk q7249519-bounded-by-p
    (real space function bound)
  (forall (object)
    (implies
     (q7249519-member-p space object)
     (q7249519-leq
      real
      (q7249519-absolute-value
       real
       (q7249519-function-at function object))
      bound))))

(defun-sk q7249519-bounded-function-p
    (real space function)
  (exists (bound)
    (and
     (q7249519-nonnegative-p real bound)
     (q7249519-bounded-by-p
      real space function bound))))

(defun-sk q7249519-real-open-neighborhood-p
    (real set center epsilon)
  (forall (value)
    (implies
     (and
      (q7249519-member-p real value)
      (q7249519-less
       real
       (q7249519-absolute-value
        real
        (q7249519-subtract real value center))
       epsilon))
     (q7249519-set-member-p set value))))

(defun-sk q7249519-real-open-radius-exists-p
    (real set center)
  (exists (epsilon)
    (and
     (q7249519-positive-p real epsilon)
     (q7249519-real-open-neighborhood-p
      real set center epsilon))))

(defun-sk q7249519-real-open-set-p (real set)
  (forall (center)
    (and
     (q7249519-valid-set-p real set)
     (implies
      (and
       (q7249519-member-p real center)
       (q7249519-set-member-p set center))
      (q7249519-real-open-radius-exists-p
       real set center)))))

(defun-sk q7249519-continuous-function-p
    (real space topology function)
  (forall (real-open-set)
    (implies
     (q7249519-real-open-set-p real real-open-set)
     (q7249519-open-set-p
      space topology
      (q7249519-preimage-set
       space function real-open-set)))))

(defun q7249519-bounded-continuous-p
    (real space topology function)
  (and
   (q7249519-real-function-p real space function)
   (q7249519-bounded-function-p real space function)
   (q7249519-continuous-function-p
    real space topology function)))

(defun q7249519-real-value-list-p (real values)
  (if (consp values)
      (and
       (q7249519-member-p real (car values))
       (q7249519-real-value-list-p real (cdr values)))
    (equal values nil)))

(defun q7249519-values-nonnegative-p (real values)
  (if (consp values)
      (and
       (q7249519-nonnegative-p real (car values))
       (q7249519-values-nonnegative-p
        real (cdr values)))
    (equal values nil)))

(defun-sk q7249519-range-in-values-p
    (space function values)
  (forall (object)
    (implies
     (q7249519-member-p space object)
     (member-equal
      (q7249519-function-at function object)
      values))))

(defun q7249519-simple-fibers-measurable-p
    (space measurable function values)
  (if (consp values)
      (and
       (q7249519-family-member-p
        measurable
        (q7249519-fiber-set
         space function (car values)))
       (q7249519-simple-fibers-measurable-p
        space measurable function (cdr values)))
    (equal values nil)))

(defun q7249519-simple-function-p
    (real space measurable function values)
  (and
   (true-listp values)
   (no-duplicatesp-equal values)
   (q7249519-real-value-list-p real values)
   (q7249519-values-nonnegative-p real values)
   (q7249519-real-function-p real space function)
   (q7249519-range-in-values-p
    space function values)
   (q7249519-simple-fibers-measurable-p
    space measurable function values)))

(defun q7249519-simple-integral
    (real space measure function values)
  (if (consp values)
      (q7249519-add
       real
       (q7249519-multiply
        real
        (car values)
        (q7249519-measure-value
         measure
         (q7249519-fiber-set
          space function (car values))))
       (q7249519-simple-integral
        real space measure function (cdr values)))
    (q7249519-zero real)))

(defun-sk q7249519-simple-below-p
    (real space simple function)
  (forall (object)
    (implies
     (q7249519-member-p space object)
     (and
      (q7249519-nonnegative-p
       real
       (q7249519-function-at simple object))
      (q7249519-leq
       real
       (q7249519-function-at simple object)
       (q7249519-function-at function object))))))

(defun-sk q7249519-nonnegative-function-p
    (real space function)
  (forall (object)
    (implies
     (q7249519-member-p space object)
     (q7249519-nonnegative-p
      real
      (q7249519-function-at function object)))))

(defun-sk q7249519-lintegral-upper-bound-p
    (real space measurable measure function bound)
  (forall (simple values)
    (implies
     (and
      (q7249519-simple-function-p
       real space measurable simple values)
      (q7249519-simple-below-p
       real space simple function))
     (q7249519-leq
      real
      (q7249519-simple-integral
       real space measure simple values)
      bound))))

(defun-sk q7249519-lintegral-value-p
    (real space measurable measure function value)
  (forall (bound)
    (and
     (q7249519-member-p real value)
     (q7249519-lintegral-upper-bound-p
      real space measurable measure function value)
     (implies
      (and
       (q7249519-member-p real bound)
       (q7249519-lintegral-upper-bound-p
        real space measurable measure function bound))
      (q7249519-leq real value bound)))))

(defun-sk q7249519-lintegral-operation-p
    (real space measurable)
  (forall (measure function)
    (implies
     (and
      (q7249519-finite-measure-p
       real space measurable measure)
      (q7249519-real-function-p
       real space function)
      (q7249519-bounded-function-p
       real space function)
      (q7249519-nonnegative-function-p
       real space function))
     (q7249519-lintegral-value-p
      real space measurable measure function
      (q7249519-lintegral-value
       measure function)))))

(defun-sk q7249519-function-constructor-laws-p
    (real space)
  (forall (function object)
    (implies
     (q7249519-member-p space object)
     (let ((value
            (q7249519-function-at function object)))
       (and
        (equal
         (q7249519-function-at
          (q7249519-positive-part-function
           real function)
          object)
         (if (q7249519-less
              real value (q7249519-zero real))
             (q7249519-zero real)
           value))
        (equal
         (q7249519-function-at
          (q7249519-negative-part-function
           real function)
          object)
         (if (q7249519-less
              real value (q7249519-zero real))
             (q7249519-negate real value)
           (q7249519-zero real))))))))

(defun q7249519-real-integral-value
    (real measure function)
  (q7249519-subtract
   real
   (q7249519-lintegral-value
    measure
    (q7249519-positive-part-function
     real function))
   (q7249519-lintegral-value
    measure
    (q7249519-negative-part-function
     real function))))

;; The weak topology is the least topology on finite measures making every
;; bounded-continuous-test-function integral map continuous.

(defun-sk q7249519-integral-preimage-laws-p
    (real space topology measurable)
  (forall (function real-open-set measure)
    (iff
     (q7249519-set-member-p
      (q7249519-integral-preimage-set
       real space topology measurable
       function real-open-set)
      measure)
     (and
      (q7249519-finite-measure-p
       real space measurable measure)
      (q7249519-set-member-p
       real-open-set
       (q7249519-real-integral-value
        real measure function))))))

(defun-sk q7249519-weak-subbasis-contained-p
    (real space topology measurable weak-topology)
  (forall (function real-open-set)
    (implies
     (and
      (q7249519-bounded-continuous-p
       real space topology function)
      (q7249519-real-open-set-p
       real real-open-set))
     (q7249519-open-set-p
      (q7249519-finite-measure-type
       real space measurable)
      weak-topology
      (q7249519-integral-preimage-set
       real space topology measurable
       function real-open-set)))))

(defun-sk q7249519-weak-topology-minimal-p
    (real space topology measurable weak-topology)
  (forall (candidate)
    (implies
     (and
      (q7249519-topological-space-p
       (q7249519-finite-measure-type
        real space measurable)
       candidate)
      (q7249519-weak-subbasis-contained-p
       real space topology measurable candidate))
     (q7249519-family-subset-p
      weak-topology candidate))))

(defun q7249519-weak-topology-p
    (real space topology measurable weak-topology)
  (and
   (q7249519-topological-space-p
    (q7249519-finite-measure-type
     real space measurable)
    weak-topology)
   (q7249519-weak-subbasis-contained-p
    real space topology measurable weak-topology)
   (q7249519-weak-topology-minimal-p
    real space topology measurable weak-topology)))

(defun-sk q7249519-weak-topology-exists-p
    (real space topology measurable)
  (exists (weak-topology)
    (q7249519-weak-topology-p
     real space topology measurable weak-topology)))

;; The compact sequence K, its monotonicity alternative, and the target set of
;; finite measures retain the source quantifier scopes.

(defun-sk q7249519-compact-sequence-p
    (space topology compact-sequence)
  (forall (index)
    (implies
     (natp index)
     (q7249519-compact-set-p
      space topology
      (q7249519-sequence-at
       compact-sequence index)))))

(defun-sk q7249519-monotone-set-sequence-p
    (space compact-sequence)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (<= left-index right-index))
     (q7249519-set-subset-p
      space
      (q7249519-sequence-at
       compact-sequence left-index)
      (q7249519-sequence-at
       compact-sequence right-index)))))

(defun-sk q7249519-tail-bounds-p
    (real space measure u compact-sequence)
  (forall (index)
    (implies
     (natp index)
     (q7249519-leq
      real
      (q7249519-measure-value
       measure
       (q7249519-complement-set
        space
        (q7249519-sequence-at
         compact-sequence index)))
      (q7249519-sequence-at u index)))))

(defun-sk q7249519-target-set-laws-p
    (real space measurable u compact-sequence mass-bound)
  (forall (measure)
    (iff
     (q7249519-set-member-p
      (q7249519-prokhorov-target-set
       real space measurable u
       compact-sequence mass-bound)
      measure)
     (and
      (q7249519-finite-measure-p
       real space measurable measure)
      (q7249519-leq
       real
       (q7249519-measure-value
        measure (q7249519-full-set space))
       mass-bound)
      (q7249519-tail-bounds-p
       real space measure u compact-sequence)))))

(defun-sk q7249519-prokhorov-conclusion-p
    (real space topology measurable u
     compact-sequence mass-bound)
  (forall (weak-topology)
    (implies
     (q7249519-weak-topology-p
      real space topology measurable weak-topology)
     (q7249519-compact-set-p
      (q7249519-finite-measure-type
       real space measurable)
      weak-topology
      (q7249519-prokhorov-target-set
       real space measurable u
       compact-sequence mass-bound)))))

(defun-sk thousand-theorems-q7249519-prokhorov-s-theorem-statement ()
  (forall (real space topology measurable u compact-sequence mass-bound)
    (implies
     (and
      (q7249519-real-structure-p real)
      (q7249519-topological-space-p space topology)
      (q7249519-t2-space-p space topology)
      (q7249519-borel-space-p
       space topology measurable)
      (q7249519-set-constructor-laws-p real)
      (q7249519-set-constructor-laws-p space)
      (q7249519-set-constructor-laws-p
       (q7249519-finite-measure-type
        real space measurable))
      (q7249519-function-constructor-laws-p
       real space)
      (q7249519-finite-measure-carrier-laws-p
       real space measurable)
      (q7249519-lintegral-operation-p
       real space measurable)
      (q7249519-integral-preimage-laws-p
       real space topology measurable)
      (q7249519-weak-topology-exists-p
       real space topology measurable)
      (q7249519-nonnegative-p real mass-bound)
      (q7249519-nnreal-sequence-p real u)
      (q7249519-tends-to-zero-p real u)
      (q7249519-compact-sequence-p
       space topology compact-sequence)
      (or
       (q7249519-normal-space-p space topology)
       (q7249519-monotone-set-sequence-p
        space compact-sequence))
      (q7249519-target-set-laws-p
       real space measurable u
       compact-sequence mass-bound))
     (q7249519-prokhorov-conclusion-p
      real space topology measurable u
      compact-sequence mass-bound))))

(value-triple :itpeval-statement-checked)
:q
