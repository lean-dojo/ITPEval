;; Statement-only formalization of thousand-theorems corpus artifact Q842953,
;; "Lebesgue's density theorem": in a second-countable Borel metric space
;; with the Besicovitch covering property, almost every point of an arbitrary
;; set for a locally finite measure has density one in shrinking closed balls.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The conservative interfaces range over unrestricted ACL2 objects.  The
;; predicates below explicitly impose the complete ordered real field,
;; extended-nonnegative-real, metric, Borel, outer-measure, local-finiteness,
;; and Besicovitch satellite laws used in the source statement.

(defstub q842953-r-member-p (real value) t)
(defstub q842953-r-zero (real) t)
(defstub q842953-r-one (real) t)
(defstub q842953-r-add (real left right) t)
(defstub q842953-r-multiply (real left right) t)
(defstub q842953-r-negate (real value) t)
(defstub q842953-r-inverse (real value) t)
(defstub q842953-r-less (real left right) t)
(defstub q842953-r-set-member-p (real set value) t)

(defstub q842953-domain-member-p (domain value) t)
(defstub q842953-set-member-p (set value) t)
(defstub q842953-function-value (function argument) t)
(defstub q842953-set-sequence-value (sequence index) t)
(defstub q842953-measurable-set-p (measurable set) t)
(defstub q842953-measure-value (measure set) t)
(defstub q842953-distance-value (distance left right) t)
(defstub q842953-intersection-value (domain left right) t)
(defstub q842953-closed-ball-value
  (real domain distance center radius) t)

;; A Dedekind-complete ordered field, hence a presentation of the reals.

(defun q842953-r-leq (real left right)
  (not (q842953-r-less real right left)))

(defun q842953-r-subtract (real left right)
  (q842953-r-add real left (q842953-r-negate real right)))

(defun q842953-r-abs (real value)
  (if (q842953-r-less real value (q842953-r-zero real))
      (q842953-r-negate real value)
    value))

(defun-sk q842953-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q842953-r-member-p real x)
      (q842953-r-member-p real y)
      (q842953-r-member-p real z))
     (let* ((zero (q842953-r-zero real))
            (one (q842953-r-one real))
            (xy-add (q842953-r-add real x y))
            (yz-add (q842953-r-add real y z))
            (xy-mul (q842953-r-multiply real x y))
            (yz-mul (q842953-r-multiply real y z))
            (neg-x (q842953-r-negate real x))
            (inv-x (q842953-r-inverse real x)))
       (and
        (q842953-r-member-p real xy-add)
        (q842953-r-member-p real xy-mul)
        (q842953-r-member-p real neg-x)
        (q842953-r-member-p real inv-x)
        (equal
         (q842953-r-add real xy-add z)
         (q842953-r-add real x yz-add))
        (equal xy-add (q842953-r-add real y x))
        (equal (q842953-r-add real x zero) x)
        (equal (q842953-r-add real x neg-x) zero)
        (equal
         (q842953-r-multiply real xy-mul z)
         (q842953-r-multiply real x yz-mul))
        (equal xy-mul (q842953-r-multiply real y x))
        (equal (q842953-r-multiply real x one) x)
        (equal (q842953-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q842953-r-multiply real x inv-x)
          one))
        (equal
         (q842953-r-multiply
          real x (q842953-r-add real y z))
         (q842953-r-add
          real
          (q842953-r-multiply real x y)
          (q842953-r-multiply real x z))))))))

(defun-sk q842953-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q842953-r-member-p real x)
      (q842953-r-member-p real y)
      (q842953-r-member-p real z))
     (let ((zero (q842953-r-zero real)))
       (and
        (not (q842953-r-less real x x))
        (or
         (equal x y)
         (q842953-r-less real x y)
         (q842953-r-less real y x))
        (implies
         (and
          (q842953-r-less real x y)
          (q842953-r-less real y z))
         (q842953-r-less real x z))
        (implies
         (q842953-r-less real x y)
         (q842953-r-less
          real
          (q842953-r-add real x z)
          (q842953-r-add real y z)))
        (implies
         (and
          (q842953-r-less real zero x)
          (q842953-r-less real zero y))
         (q842953-r-less
          real zero
          (q842953-r-multiply real x y))))))))

(defun-sk q842953-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q842953-r-member-p real x)
     (q842953-r-set-member-p real set x))))

(defun-sk q842953-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q842953-r-member-p real x)
      (q842953-r-set-member-p real set x))
     (q842953-r-leq real x bound))))

(defun-sk q842953-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q842953-r-member-p real bound)
     (q842953-r-upper-bound-p real set bound))))

(defun-sk q842953-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q842953-r-member-p real supremum)
     (q842953-r-upper-bound-p real set supremum)
     (implies
      (and
       (q842953-r-member-p real bound)
       (q842953-r-upper-bound-p real set bound))
      (q842953-r-leq real supremum bound)))))

(defun-sk q842953-r-has-supremum-p (real set)
  (exists (supremum)
    (q842953-r-supremum-p real set supremum)))

(defun-sk q842953-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q842953-r-set-nonempty-p real set)
      (q842953-r-bounded-above-p real set))
     (q842953-r-has-supremum-p real set))))

(defun q842953-real-field-p (real)
  (let ((zero (q842953-r-zero real))
        (one (q842953-r-one real)))
    (and
     (q842953-r-member-p real zero)
     (q842953-r-member-p real one)
     (not (equal zero one))
     (q842953-r-field-laws-p real)
     (q842953-r-order-laws-p real)
     (q842953-r-less real zero one)
     (q842953-r-dedekind-complete-p real))))

;; Extended nonnegative reals with the source conventions 0 * infinity = 0,
;; 0 / 0 = 0, and infinity / infinity = 0.

(defun q842953-ennreal-p (real value)
  (or
   (equal value :q842953-top)
   (and
    (consp value)
    (equal (car value) :q842953-finite)
    (q842953-r-member-p real (cdr value))
    (q842953-r-leq
     real (q842953-r-zero real) (cdr value)))))

(defun q842953-ennreal-finite (value)
  (cons :q842953-finite value))

(defun q842953-ennreal-zero (real)
  (q842953-ennreal-finite (q842953-r-zero real)))

(defun q842953-ennreal-less (real left right)
  (cond
   ((equal left :q842953-top) nil)
   ((equal right :q842953-top) t)
   (t (q842953-r-less real (cdr left) (cdr right)))))

(defun q842953-ennreal-leq (real left right)
  (not (q842953-ennreal-less real right left)))

(defun q842953-ennreal-add (real left right)
  (if (or (equal left :q842953-top)
          (equal right :q842953-top))
      :q842953-top
    (q842953-ennreal-finite
     (q842953-r-add real (cdr left) (cdr right)))))

(defun q842953-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q842953-ennreal-zero real))
        (equal right (q842953-ennreal-zero real)))
    (q842953-ennreal-zero real))
   ((or (equal left :q842953-top)
        (equal right :q842953-top))
    :q842953-top)
   (t
    (q842953-ennreal-finite
     (q842953-r-multiply real (cdr left) (cdr right))))))

(defun q842953-ennreal-divide (real numerator denominator)
  (cond
   ((equal numerator (q842953-ennreal-zero real))
    (q842953-ennreal-zero real))
   ((equal denominator (q842953-ennreal-zero real))
    :q842953-top)
   ((equal denominator :q842953-top)
    (q842953-ennreal-zero real))
   ((equal numerator :q842953-top)
    :q842953-top)
   (t
    (q842953-ennreal-finite
     (q842953-r-multiply
      real
      (cdr numerator)
      (q842953-r-inverse real (cdr denominator)))))))

;; Arbitrary subsets, sigma algebras, and countably additive measures.

(defun-sk q842953-valid-set-p (domain set)
  (forall (x)
    (implies
     (q842953-set-member-p set x)
     (q842953-domain-member-p domain x))))

(defun-sk q842953-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q842953-domain-member-p domain x)
     (iff
      (q842953-set-member-p left x)
      (q842953-set-member-p right x)))))

(defun-sk q842953-subset-p (domain left right)
  (forall (x)
    (implies
     (and
      (q842953-domain-member-p domain x)
      (q842953-set-member-p left x))
     (q842953-set-member-p right x))))

(defun-sk q842953-intersection-set-p
    (domain left right intersection)
  (forall (x)
    (iff
     (q842953-set-member-p intersection x)
     (and
      (q842953-domain-member-p domain x)
      (q842953-set-member-p left x)
      (q842953-set-member-p right x)))))

(defun-sk q842953-intersection-operation-p (domain)
  (forall (left right)
    (implies
     (and
      (q842953-valid-set-p domain left)
      (q842953-valid-set-p domain right))
     (q842953-intersection-set-p
      domain left right
      (q842953-intersection-value domain left right)))))

(defun-sk q842953-empty-set-p (domain set)
  (forall (x)
    (implies
     (q842953-domain-member-p domain x)
     (not (q842953-set-member-p set x)))))

(defun-sk q842953-complement-set-p (domain set complement)
  (forall (x)
    (implies
     (q842953-domain-member-p domain x)
     (iff
      (q842953-set-member-p complement x)
      (not (q842953-set-member-p set x))))))

(defun-sk q842953-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q842953-valid-set-p
      domain (q842953-set-sequence-value sequence n)))))

(defun-sk q842953-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q842953-set-member-p
      (q842953-set-sequence-value sequence n)
      x))))

(defun-sk q842953-sequence-union-set-p (domain sequence union)
  (forall (x)
    (implies
     (q842953-domain-member-p domain x)
     (iff
      (q842953-set-member-p union x)
      (q842953-sequence-union-member-p sequence x)))))

(defun-sk q842953-measurable-sequence-p
    (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q842953-measurable-set-p
      measurable
      (q842953-set-sequence-value sequence n)))))

(defun-sk q842953-sigma-extensional-p
    (domain measurable)
  (forall (left right)
    (implies
     (q842953-set-equiv-p domain left right)
     (iff
      (q842953-measurable-set-p measurable left)
      (q842953-measurable-set-p measurable right)))))

(defun-sk q842953-sigma-valid-p (domain measurable)
  (forall (set)
    (implies
     (q842953-measurable-set-p measurable set)
     (q842953-valid-set-p domain set))))

(defun-sk q842953-measurable-empty-exists-p
    (domain measurable)
  (exists (empty)
    (and
     (q842953-empty-set-p domain empty)
     (q842953-measurable-set-p measurable empty))))

(defun-sk q842953-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q842953-complement-set-p domain set complement)
     (q842953-measurable-set-p measurable complement))))

(defun-sk q842953-measurable-complements-p (domain measurable)
  (forall (set)
    (implies
     (q842953-measurable-set-p measurable set)
     (q842953-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q842953-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q842953-sequence-union-set-p domain sequence union)
     (q842953-measurable-set-p measurable union))))

(defun-sk q842953-measurable-unions-p (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q842953-set-sequence-p domain sequence)
      (q842953-measurable-sequence-p measurable sequence))
     (q842953-measurable-union-exists-p
      domain measurable sequence))))

(defun q842953-sigma-algebra-p (domain measurable)
  (and
   (q842953-sigma-extensional-p domain measurable)
   (q842953-sigma-valid-p domain measurable)
   (q842953-measurable-empty-exists-p domain measurable)
   (q842953-measurable-complements-p domain measurable)
   (q842953-measurable-unions-p domain measurable)))

(defun-sk q842953-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q842953-set-member-p left x)
      (q842953-set-member-p right x)))))

(defun-sk q842953-pairwise-disjoint-sequence-p (sequence)
  (forall (m n)
    (implies
     (and (natp m) (natp n) (not (equal m n)))
     (q842953-disjoint-sets-p
      (q842953-set-sequence-value sequence m)
      (q842953-set-sequence-value sequence n)))))

(defun q842953-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q842953-ennreal-zero real)
    (q842953-ennreal-add
     real
     (q842953-measure-prefix-sum
      real measure sequence (1- count))
     (q842953-measure-value
      measure
      (q842953-set-sequence-value sequence (1- count))))))

(defun-sk q842953-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q842953-ennreal-leq
      real
      (q842953-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q842953-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q842953-ennreal-p real total)
     (q842953-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q842953-ennreal-p real bound)
       (q842953-sum-upper-bound-p
        real measure sequence bound))
      (q842953-ennreal-leq real total bound)))))

(defun-sk q842953-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q842953-set-equiv-p domain left right)
     (equal
      (q842953-measure-value measure left)
      (q842953-measure-value measure right)))))

(defun-sk q842953-measure-values-p (real domain measure)
  (forall (set)
    (implies
     (q842953-valid-set-p domain set)
     (q842953-ennreal-p
      real (q842953-measure-value measure set)))))

(defun-sk q842953-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q842953-empty-set-p domain empty)
     (equal
      (q842953-measure-value measure empty)
      (q842953-ennreal-zero real)))))

(defun-sk q842953-measure-monotone-p
    (real domain measure)
  (forall (left right)
    (implies
     (and
      (q842953-valid-set-p domain left)
      (q842953-valid-set-p domain right)
      (q842953-subset-p domain left right))
     (q842953-ennreal-leq
      real
      (q842953-measure-value measure left)
      (q842953-measure-value measure right)))))

(defun-sk q842953-countably-subadditive-p
    (real domain measure)
  (forall (sequence union total)
    (implies
     (and
      (q842953-set-sequence-p domain sequence)
      (q842953-sequence-union-set-p domain sequence union)
      (q842953-countable-sum-p real measure sequence total))
     (q842953-ennreal-leq
      real
      (q842953-measure-value measure union)
      total))))

(defun-sk q842953-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q842953-set-sequence-p domain sequence)
      (q842953-measurable-sequence-p measurable sequence)
      (q842953-pairwise-disjoint-sequence-p sequence)
      (q842953-sequence-union-set-p domain sequence union))
     (q842953-countable-sum-p
      real measure sequence
      (q842953-measure-value measure union)))))

(defun-sk q842953-measurable-hull-exists-p
    (domain measurable measure set)
  (exists (hull)
    (and
     (q842953-measurable-set-p measurable hull)
     (q842953-subset-p domain set hull)
     (equal
      (q842953-measure-value measure hull)
      (q842953-measure-value measure set)))))

(defun-sk q842953-measurable-hulls-p
    (domain measurable measure)
  (forall (set)
    (implies
     (q842953-valid-set-p domain set)
     (q842953-measurable-hull-exists-p
      domain measurable measure set))))

(defun q842953-measure-space-p
    (real domain measurable measure)
  (and
   (q842953-sigma-algebra-p domain measurable)
   (q842953-measure-extensional-p domain measure)
   (q842953-measure-values-p real domain measure)
   (q842953-measure-empty-zero-p real domain measure)
   (q842953-measure-monotone-p real domain measure)
   (q842953-countably-subadditive-p real domain measure)
   (q842953-countably-additive-p
    real domain measurable measure)
   (q842953-measurable-hulls-p
    domain measurable measure)))

;; Metric topology, second countability, its Borel sigma algebra, and
;; local finiteness.

(defun-sk q842953-pseudometric-laws-p
    (real domain distance)
  (forall (x y z)
    (implies
     (and
      (q842953-domain-member-p domain x)
      (q842953-domain-member-p domain y)
      (q842953-domain-member-p domain z))
     (let ((dxy (q842953-distance-value distance x y))
           (dyz (q842953-distance-value distance y z))
           (dxz (q842953-distance-value distance x z)))
       (and
        (q842953-r-member-p real dxy)
        (q842953-r-member-p real dyz)
        (q842953-r-member-p real dxz)
        (q842953-r-leq real (q842953-r-zero real) dxy)
        (equal
         (q842953-distance-value distance x x)
         (q842953-r-zero real))
        (equal dxy (q842953-distance-value distance y x))
        (q842953-r-leq
         real dxz (q842953-r-add real dxy dyz)))))))

(defun-sk q842953-metric-separation-p
    (real domain distance)
  (forall (x y)
    (implies
     (and
      (q842953-domain-member-p domain x)
      (q842953-domain-member-p domain y))
     (iff
      (equal
       (q842953-distance-value distance x y)
       (q842953-r-zero real))
      (equal x y)))))

(defun q842953-metric-space-p (real domain distance)
  (and
   (q842953-pseudometric-laws-p real domain distance)
   (q842953-metric-separation-p real domain distance)))

(defun-sk q842953-open-ball-p
    (real domain distance center radius set)
  (forall (x)
    (implies
     (q842953-domain-member-p domain x)
     (iff
      (q842953-set-member-p set x)
      (q842953-r-less
       real
       (q842953-distance-value distance x center)
       radius)))))

(defun-sk q842953-closed-ball-subset-p
    (real domain distance center radius set)
  (forall (x)
    (implies
     (and
      (q842953-domain-member-p domain x)
      (q842953-r-leq
       real
       (q842953-distance-value distance x center)
       radius))
     (q842953-set-member-p set x))))

(defun-sk q842953-set-subset-closed-ball-p
    (real domain distance set center radius)
  (forall (x)
    (implies
     (and
      (q842953-domain-member-p domain x)
      (q842953-set-member-p set x))
     (q842953-r-leq
      real
      (q842953-distance-value distance x center)
      radius))))

(defun-sk q842953-open-radius-exists-p
    (real domain distance set x)
  (exists (radius)
    (and
     (q842953-r-member-p real radius)
     (q842953-r-less
      real (q842953-r-zero real) radius)
     (q842953-closed-ball-subset-p
      real domain distance x radius set))))

(defun-sk q842953-metric-open-interior-p
    (real domain distance set)
  (forall (x)
    (implies
     (and
      (q842953-domain-member-p domain x)
      (q842953-set-member-p set x))
     (q842953-open-radius-exists-p
      real domain distance set x))))

(defun q842953-metric-open-p (real domain distance set)
  (and
   (q842953-valid-set-p domain set)
   (q842953-metric-open-interior-p
    real domain distance set)))

(defun-sk q842953-basis-open-p
    (real domain distance basis)
  (forall (n)
    (implies
     (natp n)
     (q842953-metric-open-p
      real domain distance
      (q842953-set-sequence-value basis n)))))

(defun-sk q842953-basis-refinement-exists-p
    (domain basis set x)
  (exists (n)
    (and
     (natp n)
     (q842953-set-member-p
      (q842953-set-sequence-value basis n)
      x)
     (q842953-subset-p
      domain
      (q842953-set-sequence-value basis n)
      set))))

(defun-sk q842953-basis-refines-p
    (real domain distance basis)
  (forall (set x)
    (implies
     (and
      (q842953-metric-open-p real domain distance set)
      (q842953-domain-member-p domain x)
      (q842953-set-member-p set x))
     (q842953-basis-refinement-exists-p
      domain basis set x))))

(defun q842953-second-countable-basis-p
    (real domain distance basis)
  (and
   (q842953-set-sequence-p domain basis)
   (q842953-basis-open-p real domain distance basis)
   (q842953-basis-refines-p real domain distance basis)))

(defun-sk q842953-second-countable-p
    (real domain distance)
  (exists (basis)
    (q842953-second-countable-basis-p
     real domain distance basis)))

(defun-sk q842953-all-opens-measurable-p
    (real domain distance measurable)
  (forall (set)
    (implies
     (q842953-metric-open-p real domain distance set)
     (q842953-measurable-set-p measurable set))))

(defun-sk q842953-borel-minimal-p
    (real domain distance measurable)
  (forall (other set)
    (implies
     (and
      (q842953-sigma-algebra-p domain other)
      (q842953-all-opens-measurable-p
       real domain distance other)
      (q842953-measurable-set-p measurable set))
     (q842953-measurable-set-p other set))))

(defun q842953-borel-space-p
    (real domain distance measurable)
  (and
   (q842953-sigma-algebra-p domain measurable)
   (q842953-all-opens-measurable-p
    real domain distance measurable)
   (q842953-borel-minimal-p
    real domain distance measurable)))

(defun-sk q842953-finite-ball-exists-p
    (real domain distance measurable measure x)
  (exists (radius ball)
    (and
     (q842953-r-member-p real radius)
     (q842953-r-less
      real (q842953-r-zero real) radius)
     (q842953-open-ball-p
      real domain distance x radius ball)
     (q842953-measurable-set-p measurable ball)
     (not
      (equal
       (q842953-measure-value measure ball)
       :q842953-top)))))

(defun-sk q842953-locally-finite-measure-p
    (real domain distance measurable measure)
  (forall (x)
    (implies
     (q842953-domain-member-p domain x)
     (q842953-finite-ball-exists-p
      real domain distance measurable measure x))))

;; Exact closed balls.

(defun-sk q842953-closed-ball-set-p
    (real domain distance center radius ball)
  (forall (x)
    (iff
     (q842953-set-member-p ball x)
     (and
      (q842953-domain-member-p domain x)
      (q842953-r-leq
       real
       (q842953-distance-value distance x center)
       radius)))))

(defun-sk q842953-closed-ball-operation-p
    (real domain distance)
  (forall (center radius)
    (implies
     (and
      (q842953-domain-member-p domain center)
      (q842953-r-member-p real radius))
     (q842953-closed-ball-set-p
      real domain distance center radius
      (q842953-closed-ball-value
       real domain distance center radius)))))

;; The source's HasBesicovitchCovering class: for some N and tau > 1,
;; no N+1 positive-radius satellite configuration exists.  Finite functions
;; on Fin (N+1) are represented exactly by lists of length N+1.

(defun-sk q842953-center-list-values-p
    (domain centers n)
  (forall (i)
    (implies
     (and (natp i) (<= i n))
     (q842953-domain-member-p domain (nth i centers)))))

(defun-sk q842953-radius-list-values-p
    (real radii n)
  (forall (i)
    (implies
     (and (natp i) (<= i n))
     (and
      (q842953-r-member-p real (nth i radii))
      (q842953-r-less
       real (q842953-r-zero real) (nth i radii))))))

(defun-sk q842953-satellite-pair-laws-p
    (real domain distance tau centers radii n)
  (forall (i j)
    (implies
     (and
      (natp i)
      (natp j)
      (<= i n)
      (<= j n)
      (not (equal i j)))
     (or
      (and
       (q842953-r-leq
        real
        (nth i radii)
        (q842953-distance-value
         distance (nth i centers) (nth j centers)))
       (q842953-r-leq
        real
        (nth j radii)
        (q842953-r-multiply real tau (nth i radii))))
      (and
       (q842953-r-leq
        real
        (nth j radii)
        (q842953-distance-value
         distance (nth j centers) (nth i centers)))
       (q842953-r-leq
        real
        (nth i radii)
        (q842953-r-multiply real tau (nth j radii))))))))

(defun-sk q842953-satellite-last-laws-p
    (real distance tau centers radii n)
  (forall (i)
    (implies
     (and (natp i) (< i n))
     (and
      (q842953-r-leq
       real
       (nth i radii)
       (q842953-distance-value
        distance (nth i centers) (nth n centers)))
      (q842953-r-leq
       real
       (nth n radii)
       (q842953-r-multiply real tau (nth i radii)))
      (q842953-r-leq
       real
       (q842953-distance-value
        distance (nth i centers) (nth n centers))
       (q842953-r-add
        real (nth i radii) (nth n radii)))))))

(defun q842953-satellite-configuration-p
    (real domain distance n tau centers radii)
  (and
   (natp n)
   (true-listp centers)
   (true-listp radii)
   (equal (len centers) (+ 1 n))
   (equal (len radii) (+ 1 n))
   (q842953-center-list-values-p domain centers n)
   (q842953-radius-list-values-p real radii n)
   (q842953-satellite-pair-laws-p
    real domain distance tau centers radii n)
   (q842953-satellite-last-laws-p
    real distance tau centers radii n)))

(defun-sk q842953-satellite-configuration-exists-p
    (real domain distance n tau)
  (exists (centers radii)
    (q842953-satellite-configuration-p
     real domain distance n tau centers radii)))

(defun-sk q842953-has-besicovitch-covering-p
    (real domain distance)
  (exists (n tau)
    (and
     (natp n)
     (q842953-r-member-p real tau)
     (q842953-r-less real (q842953-r-one real) tau)
     (not
      (q842953-satellite-configuration-exists-p
       real domain distance n tau)))))

;; Density quotient in extended nonnegative reals, using the source
;; conventions 0/0 = 0, infinity/infinity = 0, and positive/0 = infinity.

(defun q842953-density-ratio
    (real domain distance measure source point radius)
  (let* ((ball
          (q842953-closed-ball-value
           real domain distance point radius))
         (inside
          (q842953-intersection-value domain source ball)))
    (q842953-ennreal-divide
     real
     (q842953-measure-value measure inside)
     (q842953-measure-value measure ball))))

(defun-sk q842953-density-radii-close-p
    (real domain distance measure source point epsilon delta)
  (forall (radius)
    (implies
     (and
      (q842953-r-member-p real radius)
      (q842953-r-less
       real (q842953-r-zero real) radius)
      (q842953-r-less real radius delta))
     (let ((ratio
            (q842953-density-ratio
             real domain distance measure source point radius)))
       (and
        (q842953-ennreal-p real ratio)
        (not (equal ratio :q842953-top))
        (q842953-r-less
         real
         (q842953-r-abs
          real
          (q842953-r-subtract
           real
           (cdr ratio)
           (q842953-r-one real)))
         epsilon))))))

(defun-sk q842953-density-delta-exists-p
    (real domain distance measure source point epsilon)
  (exists (delta)
    (and
     (q842953-r-member-p real delta)
     (q842953-r-less
      real (q842953-r-zero real) delta)
     (q842953-density-radii-close-p
      real domain distance measure source point epsilon delta))))

(defun-sk q842953-density-tends-to-one-p
    (real domain distance measure source point)
  (forall (epsilon)
    (implies
     (and
      (q842953-r-member-p real epsilon)
      (q842953-r-less
       real (q842953-r-zero real) epsilon))
     (q842953-density-delta-exists-p
      real domain distance measure source point epsilon))))

;; The failure set is intersected with the arbitrary source set.  Its
;; restricted-measure outer value is zero exactly when it has a measurable
;; cover whose intersection with the source has original outer measure zero.

(defun-sk q842953-bad-density-set-p
    (real domain distance measure source bad)
  (forall (x)
    (iff
     (q842953-set-member-p bad x)
     (and
      (q842953-domain-member-p domain x)
      (q842953-set-member-p source x)
      (not
       (q842953-density-tends-to-one-p
        real domain distance measure source x))))))

(defun q842953-ae-density-data-p
    (real domain distance measurable measure source bad cover)
  (and
   (q842953-valid-set-p domain bad)
   (q842953-bad-density-set-p
    real domain distance measure source bad)
   (q842953-measurable-set-p measurable cover)
   (q842953-subset-p domain bad cover)
   (equal
    (q842953-measure-value
     measure
     (q842953-intersection-value domain cover source))
    (q842953-ennreal-zero real))))

(defun-sk q842953-ae-density-p
    (real domain distance measurable measure source)
  (exists (bad cover)
    (q842953-ae-density-data-p
     real domain distance measurable measure source bad cover)))

(defun-sk thousand-theorems-q842953-lebesgue-density-statement ()
  (forall (real domain distance measurable measure source)
    (implies
     (and
      (q842953-real-field-p real)
      (q842953-valid-set-p domain source)
      (q842953-intersection-operation-p domain)
      (q842953-metric-space-p real domain distance)
      (q842953-closed-ball-operation-p
       real domain distance)
      (q842953-second-countable-p
       real domain distance)
      (q842953-borel-space-p
       real domain distance measurable)
      (q842953-measure-space-p
       real domain measurable measure)
      (q842953-locally-finite-measure-p
       real domain distance measurable measure)
      (q842953-has-besicovitch-covering-p
       real domain distance))
     (q842953-ae-density-p
      real domain distance measurable measure source))))

(value-triple :itpeval-statement-checked)
:q
