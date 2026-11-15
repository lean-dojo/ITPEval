;; Statement-only formalization of thousand-theorems corpus artifact Q2275191,
;; "Lebesgue differentiation theorem": normalized lower Lebesgue integrals
;; along a Vitali family converge almost everywhere to an almost-everywhere
;; measurable extended-nonnegative function of finite integral.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The conservative interfaces range over unrestricted ACL2 objects.  The
;; predicates below explicitly impose the complete ordered real field,
;; extended-nonnegative-real, pseudometric, Borel, measure, lower-integral,
;; local-finiteness, and Vitali-family laws used in the source statement.

(defstub q2275191-r-member-p (real value) t)
(defstub q2275191-r-zero (real) t)
(defstub q2275191-r-one (real) t)
(defstub q2275191-r-add (real left right) t)
(defstub q2275191-r-multiply (real left right) t)
(defstub q2275191-r-negate (real value) t)
(defstub q2275191-r-inverse (real value) t)
(defstub q2275191-r-less (real left right) t)
(defstub q2275191-r-set-member-p (real set value) t)

(defstub q2275191-domain-member-p (domain value) t)
(defstub q2275191-set-member-p (set value) t)
(defstub q2275191-function-value (function argument) t)
(defstub q2275191-set-sequence-value (sequence index) t)
(defstub q2275191-measurable-set-p (measurable set) t)
(defstub q2275191-measure-value (measure set) t)
(defstub q2275191-distance-value (distance left right) t)
(defstub q2275191-family-member-p (families point set) t)
(defstub q2275191-selection-member-p (selection center set) t)
(defstub q2275191-lintegral-value
  (lintegral real domain measurable measure function) t)

;; A Dedekind-complete ordered field, hence a presentation of the reals.

(defun q2275191-r-leq (real left right)
  (not (q2275191-r-less real right left)))

(defun q2275191-r-subtract (real left right)
  (q2275191-r-add real left (q2275191-r-negate real right)))

(defun q2275191-r-abs (real value)
  (if (q2275191-r-less real value (q2275191-r-zero real))
      (q2275191-r-negate real value)
    value))

(defun-sk q2275191-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2275191-r-member-p real x)
      (q2275191-r-member-p real y)
      (q2275191-r-member-p real z))
     (let* ((zero (q2275191-r-zero real))
            (one (q2275191-r-one real))
            (xy-add (q2275191-r-add real x y))
            (yz-add (q2275191-r-add real y z))
            (xy-mul (q2275191-r-multiply real x y))
            (yz-mul (q2275191-r-multiply real y z))
            (neg-x (q2275191-r-negate real x))
            (inv-x (q2275191-r-inverse real x)))
       (and
        (q2275191-r-member-p real xy-add)
        (q2275191-r-member-p real xy-mul)
        (q2275191-r-member-p real neg-x)
        (q2275191-r-member-p real inv-x)
        (equal
         (q2275191-r-add real xy-add z)
         (q2275191-r-add real x yz-add))
        (equal xy-add (q2275191-r-add real y x))
        (equal (q2275191-r-add real x zero) x)
        (equal (q2275191-r-add real x neg-x) zero)
        (equal
         (q2275191-r-multiply real xy-mul z)
         (q2275191-r-multiply real x yz-mul))
        (equal xy-mul (q2275191-r-multiply real y x))
        (equal (q2275191-r-multiply real x one) x)
        (equal (q2275191-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q2275191-r-multiply real x inv-x)
          one))
        (equal
         (q2275191-r-multiply
          real x (q2275191-r-add real y z))
         (q2275191-r-add
          real
          (q2275191-r-multiply real x y)
          (q2275191-r-multiply real x z))))))))

(defun-sk q2275191-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2275191-r-member-p real x)
      (q2275191-r-member-p real y)
      (q2275191-r-member-p real z))
     (let ((zero (q2275191-r-zero real)))
       (and
        (not (q2275191-r-less real x x))
        (or
         (equal x y)
         (q2275191-r-less real x y)
         (q2275191-r-less real y x))
        (implies
         (and
          (q2275191-r-less real x y)
          (q2275191-r-less real y z))
         (q2275191-r-less real x z))
        (implies
         (q2275191-r-less real x y)
         (q2275191-r-less
          real
          (q2275191-r-add real x z)
          (q2275191-r-add real y z)))
        (implies
         (and
          (q2275191-r-less real zero x)
          (q2275191-r-less real zero y))
         (q2275191-r-less
          real zero
          (q2275191-r-multiply real x y))))))))

(defun-sk q2275191-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q2275191-r-member-p real x)
     (q2275191-r-set-member-p real set x))))

(defun-sk q2275191-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q2275191-r-member-p real x)
      (q2275191-r-set-member-p real set x))
     (q2275191-r-leq real x bound))))

(defun-sk q2275191-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q2275191-r-member-p real bound)
     (q2275191-r-upper-bound-p real set bound))))

(defun-sk q2275191-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q2275191-r-member-p real supremum)
     (q2275191-r-upper-bound-p real set supremum)
     (implies
      (and
       (q2275191-r-member-p real bound)
       (q2275191-r-upper-bound-p real set bound))
      (q2275191-r-leq real supremum bound)))))

(defun-sk q2275191-r-has-supremum-p (real set)
  (exists (supremum)
    (q2275191-r-supremum-p real set supremum)))

(defun-sk q2275191-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q2275191-r-set-nonempty-p real set)
      (q2275191-r-bounded-above-p real set))
     (q2275191-r-has-supremum-p real set))))

(defun q2275191-real-field-p (real)
  (let ((zero (q2275191-r-zero real))
        (one (q2275191-r-one real)))
    (and
     (q2275191-r-member-p real zero)
     (q2275191-r-member-p real one)
     (not (equal zero one))
     (q2275191-r-field-laws-p real)
     (q2275191-r-order-laws-p real)
     (q2275191-r-less real zero one)
     (q2275191-r-dedekind-complete-p real))))

;; Extended nonnegative reals with the source conventions 0 * infinity = 0,
;; 0 / 0 = 0, and infinity / infinity = 0.

(defun q2275191-ennreal-p (real value)
  (or
   (equal value :q2275191-top)
   (and
    (consp value)
    (equal (car value) :q2275191-finite)
    (q2275191-r-member-p real (cdr value))
    (q2275191-r-leq
     real (q2275191-r-zero real) (cdr value)))))

(defun q2275191-ennreal-finite (value)
  (cons :q2275191-finite value))

(defun q2275191-ennreal-zero (real)
  (q2275191-ennreal-finite (q2275191-r-zero real)))

(defun q2275191-ennreal-less (real left right)
  (cond
   ((equal left :q2275191-top) nil)
   ((equal right :q2275191-top) t)
   (t (q2275191-r-less real (cdr left) (cdr right)))))

(defun q2275191-ennreal-leq (real left right)
  (not (q2275191-ennreal-less real right left)))

(defun q2275191-ennreal-add (real left right)
  (if (or (equal left :q2275191-top)
          (equal right :q2275191-top))
      :q2275191-top
    (q2275191-ennreal-finite
     (q2275191-r-add real (cdr left) (cdr right)))))

(defun q2275191-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q2275191-ennreal-zero real))
        (equal right (q2275191-ennreal-zero real)))
    (q2275191-ennreal-zero real))
   ((or (equal left :q2275191-top)
        (equal right :q2275191-top))
    :q2275191-top)
   (t
    (q2275191-ennreal-finite
     (q2275191-r-multiply real (cdr left) (cdr right))))))

(defun q2275191-ennreal-divide (real numerator denominator)
  (cond
   ((equal numerator (q2275191-ennreal-zero real))
    (q2275191-ennreal-zero real))
   ((equal denominator (q2275191-ennreal-zero real))
    :q2275191-top)
   ((equal denominator :q2275191-top)
    (q2275191-ennreal-zero real))
   ((equal numerator :q2275191-top)
    :q2275191-top)
   (t
    (q2275191-ennreal-finite
     (q2275191-r-multiply
      real
      (cdr numerator)
      (q2275191-r-inverse real (cdr denominator)))))))

;; Arbitrary subsets, sigma algebras, and countably additive measures.

(defun-sk q2275191-valid-set-p (domain set)
  (forall (x)
    (implies
     (q2275191-set-member-p set x)
     (q2275191-domain-member-p domain x))))

(defun-sk q2275191-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p left x)
      (q2275191-set-member-p right x)))))

(defun-sk q2275191-subset-p (domain left right)
  (forall (x)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-set-member-p left x))
     (q2275191-set-member-p right x))))

(defun-sk q2275191-empty-set-p (domain set)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (not (q2275191-set-member-p set x)))))

(defun-sk q2275191-complement-set-p (domain set complement)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p complement x)
      (not (q2275191-set-member-p set x))))))

(defun-sk q2275191-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q2275191-valid-set-p
      domain (q2275191-set-sequence-value sequence n)))))

(defun-sk q2275191-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q2275191-set-member-p
      (q2275191-set-sequence-value sequence n)
      x))))

(defun-sk q2275191-sequence-union-set-p (domain sequence union)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p union x)
      (q2275191-sequence-union-member-p sequence x)))))

(defun-sk q2275191-measurable-sequence-p
    (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q2275191-measurable-set-p
      measurable
      (q2275191-set-sequence-value sequence n)))))

(defun-sk q2275191-sigma-extensional-p
    (domain measurable)
  (forall (left right)
    (implies
     (q2275191-set-equiv-p domain left right)
     (iff
      (q2275191-measurable-set-p measurable left)
      (q2275191-measurable-set-p measurable right)))))

(defun-sk q2275191-sigma-valid-p (domain measurable)
  (forall (set)
    (implies
     (q2275191-measurable-set-p measurable set)
     (q2275191-valid-set-p domain set))))

(defun-sk q2275191-measurable-empty-exists-p
    (domain measurable)
  (exists (empty)
    (and
     (q2275191-empty-set-p domain empty)
     (q2275191-measurable-set-p measurable empty))))

(defun-sk q2275191-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q2275191-complement-set-p domain set complement)
     (q2275191-measurable-set-p measurable complement))))

(defun-sk q2275191-measurable-complements-p (domain measurable)
  (forall (set)
    (implies
     (q2275191-measurable-set-p measurable set)
     (q2275191-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q2275191-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q2275191-sequence-union-set-p domain sequence union)
     (q2275191-measurable-set-p measurable union))))

(defun-sk q2275191-measurable-unions-p (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q2275191-set-sequence-p domain sequence)
      (q2275191-measurable-sequence-p measurable sequence))
     (q2275191-measurable-union-exists-p
      domain measurable sequence))))

(defun q2275191-sigma-algebra-p (domain measurable)
  (and
   (q2275191-sigma-extensional-p domain measurable)
   (q2275191-sigma-valid-p domain measurable)
   (q2275191-measurable-empty-exists-p domain measurable)
   (q2275191-measurable-complements-p domain measurable)
   (q2275191-measurable-unions-p domain measurable)))

(defun-sk q2275191-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q2275191-set-member-p left x)
      (q2275191-set-member-p right x)))))

(defun-sk q2275191-pairwise-disjoint-sequence-p (sequence)
  (forall (m n)
    (implies
     (and (natp m) (natp n) (not (equal m n)))
     (q2275191-disjoint-sets-p
      (q2275191-set-sequence-value sequence m)
      (q2275191-set-sequence-value sequence n)))))

(defun q2275191-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q2275191-ennreal-zero real)
    (q2275191-ennreal-add
     real
     (q2275191-measure-prefix-sum
      real measure sequence (1- count))
     (q2275191-measure-value
      measure
      (q2275191-set-sequence-value sequence (1- count))))))

(defun-sk q2275191-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q2275191-ennreal-leq
      real
      (q2275191-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q2275191-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q2275191-ennreal-p real total)
     (q2275191-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q2275191-ennreal-p real bound)
       (q2275191-sum-upper-bound-p
        real measure sequence bound))
      (q2275191-ennreal-leq real total bound)))))

(defun-sk q2275191-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q2275191-set-equiv-p domain left right)
     (equal
      (q2275191-measure-value measure left)
      (q2275191-measure-value measure right)))))

(defun-sk q2275191-measure-values-p (real domain measure)
  (forall (set)
    (implies
     (q2275191-valid-set-p domain set)
     (q2275191-ennreal-p
      real (q2275191-measure-value measure set)))))

(defun-sk q2275191-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q2275191-empty-set-p domain empty)
     (equal
      (q2275191-measure-value measure empty)
      (q2275191-ennreal-zero real)))))

(defun-sk q2275191-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q2275191-set-sequence-p domain sequence)
      (q2275191-measurable-sequence-p measurable sequence)
      (q2275191-pairwise-disjoint-sequence-p sequence)
      (q2275191-sequence-union-set-p domain sequence union))
     (q2275191-countable-sum-p
      real measure sequence
      (q2275191-measure-value measure union)))))

(defun q2275191-measure-space-p
    (real domain measurable measure)
  (and
   (q2275191-sigma-algebra-p domain measurable)
   (q2275191-measure-extensional-p domain measure)
   (q2275191-measure-values-p real domain measure)
   (q2275191-measure-empty-zero-p real domain measure)
   (q2275191-countably-additive-p
    real domain measurable measure)))

;; Null sets use outer-measure semantics: an arbitrary set is null when it is
;; contained in a measurable set of measure zero.

(defun-sk q2275191-null-cover-p
    (real domain measurable measure bad-set)
  (exists (cover)
    (and
     (q2275191-valid-set-p domain bad-set)
     (q2275191-measurable-set-p measurable cover)
     (q2275191-subset-p domain bad-set cover)
     (equal
      (q2275191-measure-value measure cover)
      (q2275191-ennreal-zero real)))))

;; Pseudometric topology, second countability, its Borel sigma algebra, and
;; local finiteness.

(defun-sk q2275191-pseudometric-laws-p
    (real domain distance)
  (forall (x y z)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-domain-member-p domain y)
      (q2275191-domain-member-p domain z))
     (let ((dxy (q2275191-distance-value distance x y))
           (dyz (q2275191-distance-value distance y z))
           (dxz (q2275191-distance-value distance x z)))
       (and
        (q2275191-r-member-p real dxy)
        (q2275191-r-member-p real dyz)
        (q2275191-r-member-p real dxz)
        (q2275191-r-leq real (q2275191-r-zero real) dxy)
        (equal
         (q2275191-distance-value distance x x)
         (q2275191-r-zero real))
        (equal dxy (q2275191-distance-value distance y x))
        (q2275191-r-leq
         real dxz (q2275191-r-add real dxy dyz)))))))

(defun-sk q2275191-open-ball-p
    (real domain distance center radius set)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p set x)
      (q2275191-r-less
       real
       (q2275191-distance-value distance x center)
       radius)))))

(defun-sk q2275191-closed-ball-subset-p
    (real domain distance center radius set)
  (forall (x)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-r-leq
       real
       (q2275191-distance-value distance x center)
       radius))
     (q2275191-set-member-p set x))))

(defun-sk q2275191-set-subset-closed-ball-p
    (real domain distance set center radius)
  (forall (x)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-set-member-p set x))
     (q2275191-r-leq
      real
      (q2275191-distance-value distance x center)
      radius))))

(defun-sk q2275191-open-radius-exists-p
    (real domain distance set x)
  (exists (radius)
    (and
     (q2275191-r-member-p real radius)
     (q2275191-r-less
      real (q2275191-r-zero real) radius)
     (q2275191-closed-ball-subset-p
      real domain distance x radius set))))

(defun-sk q2275191-metric-open-interior-p
    (real domain distance set)
  (forall (x)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-set-member-p set x))
     (q2275191-open-radius-exists-p
      real domain distance set x))))

(defun q2275191-metric-open-p (real domain distance set)
  (and
   (q2275191-valid-set-p domain set)
   (q2275191-metric-open-interior-p
    real domain distance set)))

(defun-sk q2275191-basis-open-p
    (real domain distance basis)
  (forall (n)
    (implies
     (natp n)
     (q2275191-metric-open-p
      real domain distance
      (q2275191-set-sequence-value basis n)))))

(defun-sk q2275191-basis-refinement-exists-p
    (domain basis set x)
  (exists (n)
    (and
     (natp n)
     (q2275191-set-member-p
      (q2275191-set-sequence-value basis n)
      x)
     (q2275191-subset-p
      domain
      (q2275191-set-sequence-value basis n)
      set))))

(defun-sk q2275191-basis-refines-p
    (real domain distance basis)
  (forall (set x)
    (implies
     (and
      (q2275191-metric-open-p real domain distance set)
      (q2275191-domain-member-p domain x)
      (q2275191-set-member-p set x))
     (q2275191-basis-refinement-exists-p
      domain basis set x))))

(defun q2275191-second-countable-basis-p
    (real domain distance basis)
  (and
   (q2275191-set-sequence-p domain basis)
   (q2275191-basis-open-p real domain distance basis)
   (q2275191-basis-refines-p real domain distance basis)))

(defun-sk q2275191-second-countable-p
    (real domain distance)
  (exists (basis)
    (q2275191-second-countable-basis-p
     real domain distance basis)))

(defun-sk q2275191-all-opens-measurable-p
    (real domain distance measurable)
  (forall (set)
    (implies
     (q2275191-metric-open-p real domain distance set)
     (q2275191-measurable-set-p measurable set))))

(defun-sk q2275191-borel-minimal-p
    (real domain distance measurable)
  (forall (other set)
    (implies
     (and
      (q2275191-sigma-algebra-p domain other)
      (q2275191-all-opens-measurable-p
       real domain distance other)
      (q2275191-measurable-set-p measurable set))
     (q2275191-measurable-set-p other set))))

(defun q2275191-borel-space-p
    (real domain distance measurable)
  (and
   (q2275191-sigma-algebra-p domain measurable)
   (q2275191-all-opens-measurable-p
    real domain distance measurable)
   (q2275191-borel-minimal-p
    real domain distance measurable)))

(defun-sk q2275191-finite-ball-exists-p
    (real domain distance measurable measure x)
  (exists (radius ball)
    (and
     (q2275191-r-member-p real radius)
     (q2275191-r-less
      real (q2275191-r-zero real) radius)
     (q2275191-open-ball-p
      real domain distance x radius ball)
     (q2275191-measurable-set-p measurable ball)
     (not
      (equal
       (q2275191-measure-value measure ball)
       :q2275191-top)))))

(defun-sk q2275191-locally-finite-measure-p
    (real domain distance measurable measure)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (q2275191-finite-ball-exists-p
      real domain distance measurable measure x))))

;; Almost-everywhere measurable extended-nonnegative functions.

(defun-sk q2275191-ennreal-function-p
    (real domain function)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (q2275191-ennreal-p
      real (q2275191-function-value function x)))))

(defun-sk q2275191-upper-ray-preimage-p
    (real domain function threshold set)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p set x)
      (q2275191-ennreal-less
       real threshold
       (q2275191-function-value function x))))))

(defun-sk q2275191-upper-ray-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q2275191-upper-ray-preimage-p
      real domain function threshold set)
     (q2275191-measurable-set-p measurable set))))

(defun-sk q2275191-measurable-upper-rays-p
    (real domain measurable function)
  (forall (threshold)
    (implies
     (q2275191-ennreal-p real threshold)
     (q2275191-upper-ray-preimage-exists-p
      real domain measurable function threshold))))

(defun q2275191-measurable-ennreal-function-p
    (real domain measurable function)
  (and
   (q2275191-ennreal-function-p real domain function)
   (q2275191-measurable-upper-rays-p
    real domain measurable function)))

(defun-sk q2275191-difference-set-p
    (domain left right bad)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p bad x)
      (not
       (equal
        (q2275191-function-value left x)
        (q2275191-function-value right x)))))))

(defun q2275191-ae-equal-data-p
    (real domain measurable measure left right bad cover)
  (and
   (q2275191-valid-set-p domain bad)
   (q2275191-difference-set-p domain left right bad)
   (q2275191-measurable-set-p measurable cover)
   (q2275191-subset-p domain bad cover)
   (equal
    (q2275191-measure-value measure cover)
    (q2275191-ennreal-zero real))))

(defun-sk q2275191-ae-equal-p
    (real domain measurable measure left right)
  (exists (bad cover)
    (q2275191-ae-equal-data-p
     real domain measurable measure left right bad cover)))

(defun-sk q2275191-aemeasurable-p
    (real domain measurable measure function)
  (exists (representative)
    (and
     (q2275191-ennreal-function-p real domain function)
     (q2275191-measurable-ennreal-function-p
      real domain measurable representative)
     (q2275191-ae-equal-p
      real domain measurable measure function representative))))

;; The lower Lebesgue integral is the least upper bound of integrals of
;; measurable finite-range simple functions below the integrand.

(defun-sk q2275191-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q2275191-domain-member-p domain x)
     (equal (q2275191-function-value function x) value))))

(defun q2275191-values-attained-p
    (domain function values)
  (if (consp values)
      (and
       (q2275191-value-attained-p
        domain function (car values))
       (q2275191-values-attained-p
        domain function (cdr values)))
    (equal values nil)))

(defun q2275191-ennreal-value-list-p (real values)
  (if (consp values)
      (and
       (q2275191-ennreal-p real (car values))
       (q2275191-ennreal-value-list-p real (cdr values)))
    (equal values nil)))

(defun-sk q2275191-range-in-values-p
    (domain function values)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (member-equal
      (q2275191-function-value function x)
      values))))

(defun-sk q2275191-fiber-set-p
    (domain function value set)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p set x)
      (equal
       (q2275191-function-value function x)
       value)))))

(defun q2275191-fiber-list-p
    (domain measurable function values fibers)
  (if (consp values)
      (and
       (consp fibers)
       (q2275191-fiber-set-p
        domain function (car values) (car fibers))
       (q2275191-measurable-set-p measurable (car fibers))
       (q2275191-fiber-list-p
        domain measurable function (cdr values) (cdr fibers)))
    (equal fibers nil)))

(defun q2275191-simple-integral
    (real measure values fibers)
  (if (consp values)
      (q2275191-ennreal-add
       real
       (q2275191-ennreal-multiply
        real
        (car values)
        (q2275191-measure-value measure (car fibers)))
       (q2275191-simple-integral
        real measure (cdr values) (cdr fibers)))
    (q2275191-ennreal-zero real)))

(defun q2275191-simple-function-data-p
    (real domain measurable function values fibers)
  (and
   (true-listp values)
   (true-listp fibers)
   (no-duplicatesp-equal values)
   (q2275191-ennreal-value-list-p real values)
   (q2275191-values-attained-p domain function values)
   (q2275191-range-in-values-p domain function values)
   (q2275191-fiber-list-p
    domain measurable function values fibers)))

(defun-sk q2275191-simple-below-p
    (real domain simple function)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (q2275191-ennreal-leq
      real
      (q2275191-function-value simple x)
      (q2275191-function-value function x)))))

(defun-sk q2275191-lintegral-upper-bound-p
    (real domain measurable measure function bound)
  (forall (simple values fibers)
    (implies
     (and
      (q2275191-simple-function-data-p
       real domain measurable simple values fibers)
      (q2275191-simple-below-p
       real domain simple function))
     (q2275191-ennreal-leq
      real
      (q2275191-simple-integral
       real measure values fibers)
      bound))))

(defun-sk q2275191-lintegral-least-p
    (real domain measurable measure function value)
  (forall (bound)
    (implies
     (and
      (q2275191-ennreal-p real bound)
      (q2275191-lintegral-upper-bound-p
       real domain measurable measure function bound))
     (q2275191-ennreal-leq real value bound))))

(defun q2275191-lintegral-result-p
    (real domain measurable measure function value)
  (and
   (q2275191-ennreal-function-p real domain function)
   (q2275191-ennreal-p real value)
   (q2275191-lintegral-upper-bound-p
    real domain measurable measure function value)
   (q2275191-lintegral-least-p
    real domain measurable measure function value)))

(defun-sk q2275191-lintegral-operation-p
    (real domain measurable lintegral)
  (forall (measure function)
    (implies
     (and
      (q2275191-measure-space-p
       real domain measurable measure)
      (q2275191-ennreal-function-p real domain function))
     (q2275191-lintegral-result-p
      real domain measurable measure function
      (q2275191-lintegral-value
       lintegral real domain measurable measure function)))))

;; Function-space closure supplies the exact indicator restriction used to
;; express the set lower integral.  DEFCHOOSE keeps this auxiliary internal.

(defun-sk q2275191-restricted-function-p
    (real domain function set restricted)
  (forall (x)
    (and
     (q2275191-ennreal-function-p real domain restricted)
     (implies
      (q2275191-domain-member-p domain x)
      (equal
       (q2275191-function-value restricted x)
       (if (q2275191-set-member-p set x)
           (q2275191-function-value function x)
         (q2275191-ennreal-zero real)))))))

(defun-sk q2275191-restriction-exists-p
    (real domain function set)
  (exists (restricted)
    (q2275191-restricted-function-p
     real domain function set restricted)))

(defun-sk q2275191-function-space-closure-p
    (real domain)
  (forall (function set)
    (implies
     (and
      (q2275191-ennreal-function-p real domain function)
      (q2275191-valid-set-p domain set))
     (q2275191-restriction-exists-p
      real domain function set))))

(defchoose q2275191-restricted-function
    (restricted)
    (real domain function set)
  (q2275191-restricted-function-p
   real domain function set restricted))

(defun q2275191-normalized-integral
    (real domain measurable measure lintegral function set)
  (q2275191-ennreal-divide
   real
   (q2275191-lintegral-value
    lintegral real domain measurable measure
    (q2275191-restricted-function
     real domain function set))
   (q2275191-measure-value measure set)))

;; Full Vitali-family structure: measurable sets with nonempty interior, fine
;; at every point, and the disjoint covering property for every fine
;; point-indexed subfamily, with an outer-null uncovered remainder.

(defun-sk q2275191-family-subset-p
    (left right point)
  (forall (set)
    (implies
     (q2275191-family-member-p left point set)
     (q2275191-family-member-p right point set))))

(defun-sk q2275191-fine-set-exists-p
    (real domain distance families point radius)
  (exists (set)
    (and
     (q2275191-family-member-p families point set)
     (q2275191-set-subset-closed-ball-p
      real domain distance set point radius))))

(defun-sk q2275191-family-fine-at-p
    (real domain distance families point)
  (forall (radius)
    (implies
     (and
      (q2275191-r-member-p real radius)
      (q2275191-r-less
       real (q2275191-r-zero real) radius))
     (q2275191-fine-set-exists-p
      real domain distance families point radius))))

(defun-sk q2275191-interior-nonempty-p
    (real domain distance set)
  (exists (center radius)
    (and
     (q2275191-domain-member-p domain center)
     (q2275191-r-member-p real radius)
     (q2275191-r-less
      real (q2275191-r-zero real) radius)
     (q2275191-closed-ball-subset-p
      real domain distance center radius set))))

(defun-sk q2275191-selection-pairwise-disjoint-p
    (selection)
  (forall (left-center left-set right-center right-set)
    (implies
     (and
      (q2275191-selection-member-p
       selection left-center left-set)
      (q2275191-selection-member-p
       selection right-center right-set)
      (or
       (not (equal left-center right-center))
       (not (equal left-set right-set))))
     (q2275191-disjoint-sets-p left-set right-set))))

(defun-sk q2275191-point-covered-p (selection point)
  (exists (center set)
    (and
     (q2275191-selection-member-p selection center set)
     (q2275191-set-member-p set point))))

(defun-sk q2275191-subfamilies-fine-on-source-p
    (real domain distance families source subfamilies)
  (forall (x)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-set-member-p source x))
     (and
      (q2275191-family-subset-p subfamilies families x)
      (q2275191-family-fine-at-p
       real domain distance subfamilies x)))))

(defun-sk q2275191-selection-valid-p
    (domain source subfamilies selection)
  (forall (center set)
    (implies
     (q2275191-selection-member-p selection center set)
     (and
      (q2275191-domain-member-p domain center)
      (q2275191-set-member-p source center)
      (q2275191-family-member-p subfamilies center set)))))

(defun-sk q2275191-uncovered-in-null-cover-p
    (domain source selection null-cover)
  (forall (x)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-set-member-p source x)
      (not (q2275191-point-covered-p selection x)))
     (q2275191-set-member-p null-cover x))))

(defun q2275191-vitali-covering-data-p
    (real domain measurable measure source subfamilies selection null-cover)
  (and
   (q2275191-selection-pairwise-disjoint-p selection)
   (q2275191-selection-valid-p
    domain source subfamilies selection)
   (q2275191-measurable-set-p measurable null-cover)
   (equal
    (q2275191-measure-value measure null-cover)
    (q2275191-ennreal-zero real))
   (q2275191-uncovered-in-null-cover-p
    domain source selection null-cover)))

(defun-sk q2275191-vitali-covering-exists-p
    (real domain measurable measure source subfamilies)
  (exists (selection null-cover)
    (q2275191-vitali-covering-data-p
     real domain measurable measure source subfamilies
     selection null-cover)))

(defun-sk q2275191-vitali-covering-property-p
    (real domain distance measurable measure families)
  (forall (source subfamilies)
    (implies
     (and
      (q2275191-valid-set-p domain source)
      (q2275191-subfamilies-fine-on-source-p
       real domain distance families source subfamilies))
     (q2275191-vitali-covering-exists-p
      real domain measurable measure source subfamilies))))

(defun-sk q2275191-family-regions-p
    (real domain distance measurable families)
  (forall (x set)
    (implies
     (and
      (q2275191-domain-member-p domain x)
      (q2275191-family-member-p families x set))
     (and
      (q2275191-valid-set-p domain set)
      (q2275191-measurable-set-p measurable set)
      (q2275191-interior-nonempty-p
       real domain distance set)))))

(defun-sk q2275191-family-fine-everywhere-p
    (real domain distance families)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (q2275191-family-fine-at-p
      real domain distance families x))))

(defun q2275191-vitali-family-p
    (real domain distance measurable measure families)
  (and
   (q2275191-family-regions-p
    real domain distance measurable families)
   (q2275191-family-fine-everywhere-p
    real domain distance families)
   (q2275191-vitali-covering-property-p
    real domain distance measurable measure families)))

;; The filter at x consists of properties holding for all family sets
;; contained in a sufficiently small closed ball about x.

(defun-sk q2275191-all-small-sets-greater-p
    (real domain distance measurable families function measure lintegral
     point threshold radius)
  (forall (set)
    (implies
     (and
      (q2275191-family-member-p families point set)
      (q2275191-set-subset-closed-ball-p
       real domain distance set point radius))
     (q2275191-ennreal-less
      real threshold
      (q2275191-normalized-integral
       real domain measurable measure lintegral function set)))))

(defun-sk q2275191-eventually-greater-p
    (real domain distance measurable families function measure lintegral
     point threshold)
  (exists (radius)
    (and
     (q2275191-r-member-p real radius)
     (q2275191-r-less
      real (q2275191-r-zero real) radius)
     (q2275191-all-small-sets-greater-p
      real domain distance measurable families function measure lintegral
      point threshold radius))))

(defun-sk q2275191-all-small-sets-close-p
    (real domain distance measurable families function measure lintegral
     point limit epsilon radius)
  (forall (set)
    (implies
     (and
      (q2275191-family-member-p families point set)
      (q2275191-set-subset-closed-ball-p
       real domain distance set point radius))
     (let ((value
            (q2275191-normalized-integral
             real domain measurable measure lintegral function set)))
       (and
        (q2275191-ennreal-p real value)
        (not (equal value :q2275191-top))
        (q2275191-r-less
         real
         (q2275191-r-abs
          real
          (q2275191-r-subtract
           real (cdr value) (cdr limit)))
         epsilon))))))

(defun-sk q2275191-eventually-close-p
    (real domain distance measurable families function measure lintegral
     point limit epsilon)
  (exists (radius)
    (and
     (q2275191-r-member-p real radius)
     (q2275191-r-less
      real (q2275191-r-zero real) radius)
     (q2275191-all-small-sets-close-p
      real domain distance measurable families function measure lintegral
      point limit epsilon radius))))

(defun-sk q2275191-converges-to-top-p
    (real domain distance measurable families function measure lintegral
     point)
  (forall (threshold)
    (implies
     (and
      (q2275191-ennreal-p real threshold)
      (not (equal threshold :q2275191-top)))
     (q2275191-eventually-greater-p
      real domain distance measurable families function measure lintegral
      point threshold))))

(defun-sk q2275191-converges-to-finite-p
    (real domain distance measurable families function measure lintegral
     point limit)
  (forall (epsilon)
    (implies
     (and
      (q2275191-r-member-p real epsilon)
      (q2275191-r-less
       real (q2275191-r-zero real) epsilon))
     (q2275191-eventually-close-p
      real domain distance measurable families function measure lintegral
      point limit epsilon))))

(defun q2275191-vitali-converges-p
    (real domain distance measurable families function measure lintegral
     point limit)
  (and
   (q2275191-ennreal-p real limit)
   (if (equal limit :q2275191-top)
       (q2275191-converges-to-top-p
        real domain distance measurable families function measure lintegral
        point)
     (q2275191-converges-to-finite-p
      real domain distance measurable families function measure lintegral
      point limit))))

(defun-sk q2275191-bad-convergence-set-p
    (real domain distance measurable measure families function lintegral
     bad)
  (forall (x)
    (implies
     (q2275191-domain-member-p domain x)
     (iff
      (q2275191-set-member-p bad x)
      (not
       (q2275191-vitali-converges-p
        real domain distance measurable families function measure
        lintegral x
        (q2275191-function-value function x)))))))

(defun q2275191-ae-vitali-convergence-data-p
    (real domain distance measurable measure families function lintegral
     bad cover)
  (and
   (q2275191-valid-set-p domain bad)
   (q2275191-bad-convergence-set-p
    real domain distance measurable measure families function lintegral
    bad)
   (q2275191-measurable-set-p measurable cover)
   (q2275191-subset-p domain bad cover)
   (equal
    (q2275191-measure-value measure cover)
    (q2275191-ennreal-zero real))))

(defun-sk q2275191-ae-vitali-convergence-p
    (real domain distance measurable measure families function lintegral)
  (exists (bad cover)
    (q2275191-ae-vitali-convergence-data-p
     real domain distance measurable measure families function lintegral
     bad cover)))

(defun-sk thousand-theorems-q2275191-lebesgue-differentiation-statement ()
  (forall
      (real domain distance measurable measure families lintegral function)
    (implies
     (and
      (q2275191-real-field-p real)
      (q2275191-pseudometric-laws-p real domain distance)
      (q2275191-second-countable-p real domain distance)
      (q2275191-borel-space-p
       real domain distance measurable)
      (q2275191-measure-space-p
       real domain measurable measure)
      (q2275191-locally-finite-measure-p
       real domain distance measurable measure)
      (q2275191-lintegral-operation-p
       real domain measurable lintegral)
      (q2275191-function-space-closure-p real domain)
      (q2275191-vitali-family-p
       real domain distance measurable measure families)
      (q2275191-aemeasurable-p
       real domain measurable measure function)
      (not
       (equal
        (q2275191-lintegral-value
         lintegral real domain measurable measure function)
        :q2275191-top)))
     (q2275191-ae-vitali-convergence-p
      real domain distance measurable measure families function lintegral))))

(value-triple :itpeval-statement-checked)
:q
