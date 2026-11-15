;; Statement-only formalization of thousand-theorems corpus artifact Q3229352,
;; "Vitali covering theorem": in an arbitrary second-countable pseudometric
;; measurable space with a locally finite measure, a fine family of closed
;; sets satisfying the stated ball and measure bounds has a countable
;; pairwise-disjoint subfamily covering the given set almost everywhere.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces range over unrestricted ACL2 objects.  The
;; predicates below explicitly present the source's real numbers, arbitrary
;; carriers, extensional sets and functions, pseudometric topology, sigma
;; algebra, outer-measure semantics, and all theorem hypotheses.  The
;; disjoint countable subfamily remains internally existential.

;; Arbitrary carriers, sets, functions, families, sequences, and measures.

(defstub q3229352-carrier-member-p (carrier value) t)
(defstub q3229352-set-member-p (set value) t)
(defstub q3229352-function-value (function argument) t)
(defstub q3229352-family-value (family index) t)
(defstub q3229352-set-sequence-value (sequence index) t)
(defstub q3229352-measurable-set-p (measurable set) t)
(defstub q3229352-measure-value (measure set) t)
(defstub q3229352-distance-value (distance left right) t)
(defstub q3229352-closed-ball-value
  (real carrier distance center radius) t)

;; A Dedekind-complete ordered-field presentation of the real numbers.

(defstub q3229352-r-member-p (real value) t)
(defstub q3229352-r-zero (real) t)
(defstub q3229352-r-one (real) t)
(defstub q3229352-r-add (real left right) t)
(defstub q3229352-r-multiply (real left right) t)
(defstub q3229352-r-negate (real value) t)
(defstub q3229352-r-inverse (real value) t)
(defstub q3229352-r-less (real left right) t)
(defstub q3229352-r-set-member-p (real set value) t)

(defun q3229352-r-leq (real left right)
  (not (q3229352-r-less real right left)))

(defun q3229352-r-three (real)
  (q3229352-r-add
   real
   (q3229352-r-one real)
   (q3229352-r-add
    real
    (q3229352-r-one real)
    (q3229352-r-one real))))

(defun-sk q3229352-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3229352-r-member-p real x)
      (q3229352-r-member-p real y)
      (q3229352-r-member-p real z))
     (let* ((zero (q3229352-r-zero real))
            (one (q3229352-r-one real))
            (xy-add (q3229352-r-add real x y))
            (yz-add (q3229352-r-add real y z))
            (xy-mul (q3229352-r-multiply real x y))
            (yz-mul (q3229352-r-multiply real y z))
            (neg-x (q3229352-r-negate real x))
            (inv-x (q3229352-r-inverse real x)))
       (and
        (q3229352-r-member-p real xy-add)
        (q3229352-r-member-p real xy-mul)
        (q3229352-r-member-p real neg-x)
        (q3229352-r-member-p real inv-x)
        (equal
         (q3229352-r-add real xy-add z)
         (q3229352-r-add real x yz-add))
        (equal xy-add (q3229352-r-add real y x))
        (equal (q3229352-r-add real x zero) x)
        (equal (q3229352-r-add real x neg-x) zero)
        (equal
         (q3229352-r-multiply real xy-mul z)
         (q3229352-r-multiply real x yz-mul))
        (equal xy-mul (q3229352-r-multiply real y x))
        (equal (q3229352-r-multiply real x one) x)
        (equal (q3229352-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q3229352-r-multiply real x inv-x)
          one))
        (equal
         (q3229352-r-multiply
          real x (q3229352-r-add real y z))
         (q3229352-r-add
          real
          (q3229352-r-multiply real x y)
          (q3229352-r-multiply real x z))))))))

(defun-sk q3229352-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3229352-r-member-p real x)
      (q3229352-r-member-p real y)
      (q3229352-r-member-p real z))
     (let ((zero (q3229352-r-zero real)))
       (and
        (not (q3229352-r-less real x x))
        (or
         (equal x y)
         (q3229352-r-less real x y)
         (q3229352-r-less real y x))
        (implies
         (and
          (q3229352-r-less real x y)
          (q3229352-r-less real y z))
         (q3229352-r-less real x z))
        (implies
         (q3229352-r-less real x y)
         (q3229352-r-less
          real
          (q3229352-r-add real x z)
          (q3229352-r-add real y z)))
        (implies
         (and
          (q3229352-r-less real zero x)
          (q3229352-r-less real zero y))
         (q3229352-r-less
          real zero
          (q3229352-r-multiply real x y))))))))

(defun-sk q3229352-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q3229352-r-member-p real x)
     (q3229352-r-set-member-p real set x))))

(defun-sk q3229352-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q3229352-r-member-p real x)
      (q3229352-r-set-member-p real set x))
     (q3229352-r-leq real x bound))))

(defun-sk q3229352-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q3229352-r-member-p real bound)
     (q3229352-r-upper-bound-p real set bound))))

(defun-sk q3229352-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q3229352-r-member-p real supremum)
     (q3229352-r-upper-bound-p real set supremum)
     (implies
      (and
       (q3229352-r-member-p real bound)
       (q3229352-r-upper-bound-p real set bound))
      (q3229352-r-leq real supremum bound)))))

(defun-sk q3229352-r-supremum-exists-p (real set)
  (exists (supremum)
    (q3229352-r-supremum-p real set supremum)))

(defun-sk q3229352-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q3229352-r-set-nonempty-p real set)
      (q3229352-r-bounded-above-p real set))
     (q3229352-r-supremum-exists-p real set))))

(defun q3229352-real-field-p (real)
  (let ((zero (q3229352-r-zero real))
        (one (q3229352-r-one real)))
    (and
     (q3229352-r-member-p real zero)
     (q3229352-r-member-p real one)
     (not (equal zero one))
     (q3229352-r-field-laws-p real)
     (q3229352-r-order-laws-p real)
     (q3229352-r-less real zero one)
     (q3229352-r-dedekind-complete-p real))))

;; Canonical extended nonnegative reals over the presented real field.

(defun q3229352-ennreal-finite (value)
  (cons :q3229352-finite value))

(defun q3229352-ennreal-zero (real)
  (q3229352-ennreal-finite (q3229352-r-zero real)))

(defun q3229352-ennreal-p (real value)
  (or
   (equal value :q3229352-top)
   (and
    (consp value)
    (equal (car value) :q3229352-finite)
    (q3229352-r-member-p real (cdr value))
    (q3229352-r-leq
     real (q3229352-r-zero real) (cdr value)))))

(defun q3229352-ennreal-less (real left right)
  (cond
   ((equal left :q3229352-top) nil)
   ((equal right :q3229352-top) t)
   (t (q3229352-r-less real (cdr left) (cdr right)))))

(defun q3229352-ennreal-leq (real left right)
  (not (q3229352-ennreal-less real right left)))

(defun q3229352-ennreal-add (real left right)
  (if (or
       (equal left :q3229352-top)
       (equal right :q3229352-top))
      :q3229352-top
    (q3229352-ennreal-finite
     (q3229352-r-add real (cdr left) (cdr right)))))

(defun q3229352-ennreal-multiply (real left right)
  (cond
   ((or
     (equal left (q3229352-ennreal-zero real))
     (equal right (q3229352-ennreal-zero real)))
    (q3229352-ennreal-zero real))
   ((or
     (equal left :q3229352-top)
     (equal right :q3229352-top))
    :q3229352-top)
   (t
    (q3229352-ennreal-finite
     (q3229352-r-multiply real (cdr left) (cdr right))))))

;; Extensional arbitrary sets and exact set operations.

(defun-sk q3229352-valid-set-p (carrier set)
  (forall (x)
    (implies
     (q3229352-set-member-p set x)
     (q3229352-carrier-member-p carrier x))))

(defun-sk q3229352-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q3229352-carrier-member-p carrier x)
     (iff
      (q3229352-set-member-p left x)
      (q3229352-set-member-p right x)))))

(defun-sk q3229352-set-extensionality-p (carrier)
  (forall (left right)
    (implies
     (and
      (q3229352-valid-set-p carrier left)
      (q3229352-valid-set-p carrier right)
      (q3229352-set-equiv-p carrier left right))
     (equal left right))))

(defun-sk q3229352-subset-p (carrier left right)
  (forall (x)
    (implies
     (and
      (q3229352-carrier-member-p carrier x)
      (q3229352-set-member-p left x))
     (q3229352-set-member-p right x))))

(defun-sk q3229352-empty-set-p (carrier set)
  (forall (x)
    (iff
     (q3229352-set-member-p set x)
     (and (q3229352-carrier-member-p carrier x) nil))))

(defun-sk q3229352-complement-set-p
    (carrier set complement)
  (forall (x)
    (iff
     (q3229352-set-member-p complement x)
     (and
      (q3229352-carrier-member-p carrier x)
      (not (q3229352-set-member-p set x))))))

(defun-sk q3229352-intersection-set-p
    (carrier left right intersection)
  (forall (x)
    (iff
     (q3229352-set-member-p intersection x)
     (and
      (q3229352-carrier-member-p carrier x)
      (q3229352-set-member-p left x)
      (q3229352-set-member-p right x)))))

(defun-sk q3229352-difference-set-p
    (carrier left right difference)
  (forall (x)
    (iff
     (q3229352-set-member-p difference x)
     (and
      (q3229352-carrier-member-p carrier x)
      (q3229352-set-member-p left x)
      (not (q3229352-set-member-p right x))))))

(defun-sk q3229352-set-sequence-p (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (q3229352-valid-set-p
      carrier
      (q3229352-set-sequence-value sequence n)))))

(defun-sk q3229352-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q3229352-set-member-p
      (q3229352-set-sequence-value sequence n)
      x))))

(defun-sk q3229352-sequence-union-set-p
    (carrier sequence union)
  (forall (x)
    (iff
     (q3229352-set-member-p union x)
     (and
      (q3229352-carrier-member-p carrier x)
      (q3229352-sequence-union-member-p sequence x)))))

;; The pseudometric and its induced topology.

(defun-sk q3229352-pseudometric-laws-p
    (real carrier distance)
  (forall (x y z)
    (implies
     (and
      (q3229352-carrier-member-p carrier x)
      (q3229352-carrier-member-p carrier y)
      (q3229352-carrier-member-p carrier z))
     (let ((dxy (q3229352-distance-value distance x y))
           (dyz (q3229352-distance-value distance y z))
           (dxz (q3229352-distance-value distance x z))
           (zero (q3229352-r-zero real)))
       (and
        (q3229352-r-member-p real dxy)
        (q3229352-r-member-p real dyz)
        (q3229352-r-member-p real dxz)
        (q3229352-r-leq real zero dxy)
        (equal
         (q3229352-distance-value distance x x)
         zero)
        (equal dxy (q3229352-distance-value distance y x))
        (q3229352-r-leq
         real
         dxz
         (q3229352-r-add real dxy dyz)))))))

(defun-sk q3229352-open-ball-contained-p
    (real carrier distance center radius set)
  (forall (y)
    (implies
     (and
      (q3229352-carrier-member-p carrier y)
      (q3229352-r-less
       real
       (q3229352-distance-value distance center y)
       radius))
     (q3229352-set-member-p set y))))

(defun-sk q3229352-open-radius-exists-p
    (real carrier distance center set)
  (exists (radius)
    (and
     (q3229352-r-member-p real radius)
     (q3229352-r-less
      real (q3229352-r-zero real) radius)
     (q3229352-open-ball-contained-p
      real carrier distance center radius set))))

(defun-sk q3229352-open-set-p
    (real carrier distance set)
  (forall (x)
    (and
     (q3229352-valid-set-p carrier set)
     (implies
      (and
       (q3229352-carrier-member-p carrier x)
       (q3229352-set-member-p set x))
      (q3229352-open-radius-exists-p
       real carrier distance x set)))))

(defun-sk q3229352-closed-set-p
    (real carrier distance set)
  (exists (complement)
    (and
     (q3229352-complement-set-p carrier set complement)
     (q3229352-open-set-p
      real carrier distance complement))))

(defun-sk q3229352-interior-nonempty-p
    (real carrier distance set)
  (exists (open-subset x)
    (and
     (q3229352-carrier-member-p carrier x)
     (q3229352-open-set-p
      real carrier distance open-subset)
     (q3229352-set-member-p open-subset x)
     (q3229352-subset-p carrier open-subset set))))

(defun-sk q3229352-closed-ball-set-p
    (real carrier distance center radius set)
  (forall (x)
    (and
     (q3229352-valid-set-p carrier set)
     (implies
      (q3229352-carrier-member-p carrier x)
      (iff
       (q3229352-set-member-p set x)
       (q3229352-r-leq
        real
        (q3229352-distance-value distance center x)
        radius))))))

(defun-sk q3229352-closed-ball-operation-p
    (real carrier distance)
  (forall (center radius)
    (implies
     (and
      (q3229352-carrier-member-p carrier center)
      (q3229352-r-member-p real radius))
     (q3229352-closed-ball-set-p
      real carrier distance center radius
      (q3229352-closed-ball-value
       real carrier distance center radius)))))

(defun-sk q3229352-basis-entries-open-p
    (real carrier distance basis)
  (forall (n)
    (implies
     (natp n)
     (q3229352-open-set-p
      real carrier distance
      (q3229352-set-sequence-value basis n)))))

(defun-sk q3229352-basis-refinement-exists-p
    (carrier basis open-set x)
  (exists (n)
    (and
     (natp n)
     (q3229352-set-member-p
      (q3229352-set-sequence-value basis n)
      x)
     (q3229352-subset-p
      carrier
      (q3229352-set-sequence-value basis n)
      open-set))))

(defun-sk q3229352-countable-basis-p
    (real carrier distance basis)
  (forall (open-set x)
    (and
     (q3229352-basis-entries-open-p
      real carrier distance basis)
     (implies
      (and
       (q3229352-open-set-p
        real carrier distance open-set)
       (q3229352-carrier-member-p carrier x)
       (q3229352-set-member-p open-set x))
      (q3229352-basis-refinement-exists-p
       carrier basis open-set x)))))

(defun-sk q3229352-second-countable-p
    (real carrier distance)
  (exists (basis)
    (q3229352-countable-basis-p
     real carrier distance basis)))

;; Sigma algebras.

(defun-sk q3229352-measurable-family-extensional-p
    (carrier measurable)
  (forall (left right)
    (implies
     (q3229352-set-equiv-p carrier left right)
     (iff
      (q3229352-measurable-set-p measurable left)
      (q3229352-measurable-set-p measurable right)))))

(defun-sk q3229352-measurable-family-valid-p
    (carrier measurable)
  (forall (set)
    (implies
     (q3229352-measurable-set-p measurable set)
     (q3229352-valid-set-p carrier set))))

(defun-sk q3229352-measurable-empty-exists-p
    (carrier measurable)
  (exists (empty)
    (and
     (q3229352-empty-set-p carrier empty)
     (q3229352-measurable-set-p measurable empty))))

(defun-sk q3229352-measurable-complement-exists-p
    (carrier measurable set)
  (exists (complement)
    (and
     (q3229352-complement-set-p carrier set complement)
     (q3229352-measurable-set-p measurable complement))))

(defun-sk q3229352-measurable-complements-p
    (carrier measurable)
  (forall (set)
    (implies
     (q3229352-measurable-set-p measurable set)
     (q3229352-measurable-complement-exists-p
      carrier measurable set))))

(defun-sk q3229352-sequence-measurable-p
    (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q3229352-measurable-set-p
      measurable
      (q3229352-set-sequence-value sequence n)))))

(defun-sk q3229352-measurable-union-exists-p
    (carrier measurable sequence)
  (exists (union)
    (and
     (q3229352-sequence-union-set-p
      carrier sequence union)
     (q3229352-measurable-set-p measurable union))))

(defun-sk q3229352-measurable-sequence-unions-p
    (carrier measurable)
  (forall (sequence)
    (implies
     (and
      (q3229352-set-sequence-p carrier sequence)
      (q3229352-sequence-measurable-p
       measurable sequence))
     (q3229352-measurable-union-exists-p
      carrier measurable sequence))))

(defun q3229352-sigma-algebra-p (carrier measurable)
  (and
   (q3229352-measurable-family-extensional-p
    carrier measurable)
   (q3229352-measurable-family-valid-p
    carrier measurable)
   (q3229352-measurable-empty-exists-p
    carrier measurable)
   (q3229352-measurable-complements-p
    carrier measurable)
   (q3229352-measurable-sequence-unions-p
    carrier measurable)))

(defun-sk q3229352-opens-measurable-p
    (real carrier distance measurable)
  (forall (set)
    (implies
     (q3229352-open-set-p
      real carrier distance set)
     (q3229352-measurable-set-p measurable set))))

;; Countable sums of extended nonnegative reals.

(defun q3229352-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q3229352-ennreal-zero real)
    (q3229352-ennreal-add
     real
     (q3229352-measure-prefix-sum
      real measure sequence (1- count))
     (q3229352-measure-value
      measure
      (q3229352-set-sequence-value
       sequence (1- count))))))

(defun-sk q3229352-countable-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q3229352-ennreal-leq
      real
      (q3229352-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q3229352-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q3229352-ennreal-p real total)
     (q3229352-countable-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q3229352-ennreal-p real bound)
       (q3229352-countable-sum-upper-bound-p
        real measure sequence bound))
      (q3229352-ennreal-leq real total bound)))))

;; A measure is presented through its underlying outer measure, with every
;; declared measurable set satisfying the Caratheodory equality.

(defun-sk q3229352-measure-values-p
    (real carrier measure)
  (forall (set)
    (implies
     (q3229352-valid-set-p carrier set)
     (q3229352-ennreal-p
      real (q3229352-measure-value measure set)))))

(defun-sk q3229352-measure-extensional-p
    (carrier measure)
  (forall (left right)
    (implies
     (q3229352-set-equiv-p carrier left right)
     (equal
      (q3229352-measure-value measure left)
      (q3229352-measure-value measure right)))))

(defun-sk q3229352-measure-empty-zero-p
    (real carrier measure)
  (forall (empty)
    (implies
     (q3229352-empty-set-p carrier empty)
     (equal
      (q3229352-measure-value measure empty)
      (q3229352-ennreal-zero real)))))

(defun-sk q3229352-measure-monotone-p
    (real carrier measure)
  (forall (left right)
    (implies
     (and
      (q3229352-valid-set-p carrier left)
      (q3229352-valid-set-p carrier right)
      (q3229352-subset-p carrier left right))
     (q3229352-ennreal-leq
      real
      (q3229352-measure-value measure left)
      (q3229352-measure-value measure right)))))

(defun-sk q3229352-subadditive-instance-p
    (real measure sequence union)
  (exists (total)
    (and
     (q3229352-countable-sum-p
      real measure sequence total)
     (q3229352-ennreal-leq
      real
      (q3229352-measure-value measure union)
      total))))

(defun-sk q3229352-countably-subadditive-p
    (real carrier measure)
  (forall (sequence union)
    (implies
     (and
      (q3229352-set-sequence-p carrier sequence)
      (q3229352-sequence-union-set-p
       carrier sequence union))
     (q3229352-subadditive-instance-p
      real measure sequence union))))

(defun-sk q3229352-caratheodory-instance-p
    (real carrier measure measurable-set arbitrary-set)
  (exists (inside outside)
    (and
     (q3229352-intersection-set-p
      carrier arbitrary-set measurable-set inside)
     (q3229352-difference-set-p
      carrier arbitrary-set measurable-set outside)
     (equal
      (q3229352-measure-value measure arbitrary-set)
      (q3229352-ennreal-add
       real
       (q3229352-measure-value measure inside)
       (q3229352-measure-value measure outside))))))

(defun-sk q3229352-measurable-caratheodory-p
    (real carrier measurable measure)
  (forall (measurable-set arbitrary-set)
    (implies
     (and
      (q3229352-measurable-set-p
       measurable measurable-set)
      (q3229352-valid-set-p carrier arbitrary-set))
     (q3229352-caratheodory-instance-p
      real carrier measure measurable-set arbitrary-set))))

(defun q3229352-measure-space-p
    (real carrier measurable measure)
  (and
   (q3229352-sigma-algebra-p carrier measurable)
   (q3229352-measure-values-p real carrier measure)
   (q3229352-measure-extensional-p carrier measure)
   (q3229352-measure-empty-zero-p real carrier measure)
   (q3229352-measure-monotone-p real carrier measure)
   (q3229352-countably-subadditive-p
    real carrier measure)
   (q3229352-measurable-caratheodory-p
    real carrier measurable measure)))

(defun-sk q3229352-finite-open-neighborhood-exists-p
    (real carrier distance measure x)
  (exists (neighborhood)
    (and
     (q3229352-open-set-p
      real carrier distance neighborhood)
     (q3229352-set-member-p neighborhood x)
     (q3229352-ennreal-less
      real
      (q3229352-measure-value measure neighborhood)
      :q3229352-top))))

(defun-sk q3229352-locally-finite-measure-p
    (real carrier distance measure)
  (forall (x)
    (implies
     (q3229352-carrier-member-p carrier x)
     (q3229352-finite-open-neighborhood-exists-p
      real carrier distance measure x))))

;; Typing of the theorem's arbitrary functions and indexed family.

(defun-sk q3229352-real-valued-function-p
    (real domain function)
  (forall (x)
    (implies
     (q3229352-carrier-member-p domain x)
     (q3229352-r-member-p
      real (q3229352-function-value function x)))))

(defun-sk q3229352-carrier-valued-function-p
    (domain codomain function)
  (forall (x)
    (implies
     (q3229352-carrier-member-p domain x)
     (q3229352-carrier-member-p
      codomain
      (q3229352-function-value function x)))))

(defun-sk q3229352-set-valued-family-p
    (index-carrier point-carrier family)
  (forall (a)
    (implies
     (q3229352-carrier-member-p index-carrier a)
     (q3229352-valid-set-p
      point-carrier
      (q3229352-family-value family a)))))

;; The five explicit hypotheses hB, muB, ht, h't, and hf.

(defun-sk q3229352-contained-in-indexed-ball-p
    (real point-carrier index-carrier distance
     index-set radius center family)
  (forall (a)
    (implies
     (and
      (q3229352-carrier-member-p index-carrier a)
      (q3229352-set-member-p index-set a))
     (q3229352-subset-p
      point-carrier
      (q3229352-family-value family a)
      (q3229352-closed-ball-value
       real point-carrier distance
       (q3229352-function-value center a)
       (q3229352-function-value radius a))))))

(defun-sk q3229352-measure-ball-bound-p
    (real point-carrier index-carrier distance measure
     index-set coefficient radius center family)
  (forall (a)
    (implies
     (and
      (q3229352-carrier-member-p index-carrier a)
      (q3229352-set-member-p index-set a))
     (q3229352-ennreal-leq
      real
      (q3229352-measure-value
       measure
       (q3229352-closed-ball-value
        real point-carrier distance
        (q3229352-function-value center a)
        (q3229352-r-multiply
         real
         (q3229352-r-three real)
         (q3229352-function-value radius a))))
      (q3229352-ennreal-multiply
       real
       (q3229352-ennreal-finite coefficient)
       (q3229352-measure-value
        measure
        (q3229352-family-value family a)))))))

(defun-sk q3229352-family-interiors-nonempty-p
    (real point-carrier index-carrier distance index-set family)
  (forall (a)
    (implies
     (and
      (q3229352-carrier-member-p index-carrier a)
      (q3229352-set-member-p index-set a))
     (q3229352-interior-nonempty-p
      real point-carrier distance
      (q3229352-family-value family a)))))

(defun-sk q3229352-family-closed-p
    (real point-carrier index-carrier distance index-set family)
  (forall (a)
    (implies
     (and
      (q3229352-carrier-member-p index-carrier a)
      (q3229352-set-member-p index-set a))
     (q3229352-closed-set-p
      real point-carrier distance
      (q3229352-family-value family a)))))

(defun-sk q3229352-fine-witness-exists-p
    (real point-carrier index-carrier
     index-set radius center x epsilon)
  (exists (a)
    (and
     (q3229352-carrier-member-p index-carrier a)
     (q3229352-set-member-p index-set a)
     (q3229352-r-leq
      real
      (q3229352-function-value radius a)
      epsilon)
     (equal
      (q3229352-function-value center a)
      x))))

(defun-sk q3229352-fine-family-on-set-p
    (real point-carrier index-carrier
     s index-set radius center)
  (forall (x epsilon)
    (implies
     (and
      (q3229352-carrier-member-p point-carrier x)
      (q3229352-set-member-p s x)
      (q3229352-r-member-p real epsilon)
      (q3229352-r-less
       real (q3229352-r-zero real) epsilon))
     (q3229352-fine-witness-exists-p
      real point-carrier index-carrier
      index-set radius center x epsilon))))

;; Exact conclusion: an internal subset u of t is countable and pairwise
;; disjoint, and the outer measure of s minus its indexed union is zero.

(defun-sk q3229352-countable-coding-p
    (index-carrier set coding)
  (forall (a b)
    (and
     (implies
      (and
       (q3229352-carrier-member-p index-carrier a)
       (q3229352-set-member-p set a))
      (natp (q3229352-function-value coding a)))
     (implies
      (and
       (q3229352-carrier-member-p index-carrier a)
       (q3229352-carrier-member-p index-carrier b)
       (q3229352-set-member-p set a)
       (q3229352-set-member-p set b)
       (equal
        (q3229352-function-value coding a)
        (q3229352-function-value coding b)))
      (equal a b)))))

(defun-sk q3229352-countable-set-p
    (index-carrier set)
  (exists (coding)
    (q3229352-countable-coding-p
     index-carrier set coding)))

(defun-sk q3229352-disjoint-family-p
    (point-carrier index-carrier set family)
  (forall (a b x)
    (implies
     (and
      (q3229352-carrier-member-p index-carrier a)
      (q3229352-carrier-member-p index-carrier b)
      (q3229352-set-member-p set a)
      (q3229352-set-member-p set b)
      (not (equal a b))
      (q3229352-carrier-member-p point-carrier x)
      (q3229352-set-member-p
       (q3229352-family-value family a) x))
     (not
      (q3229352-set-member-p
       (q3229352-family-value family b) x)))))

(defun-sk q3229352-indexed-union-member-p
    (index-carrier set family x)
  (exists (a)
    (and
     (q3229352-carrier-member-p index-carrier a)
     (q3229352-set-member-p set a)
     (q3229352-set-member-p
      (q3229352-family-value family a)
      x))))

(defun-sk q3229352-indexed-union-set-p
    (point-carrier index-carrier set family union)
  (forall (x)
    (iff
     (q3229352-set-member-p union x)
     (and
      (q3229352-carrier-member-p point-carrier x)
      (q3229352-indexed-union-member-p
       index-carrier set family x)))))

(defun q3229352-covering-conclusion-data-p
    (real point-carrier index-carrier measure
     s index-set family u union remainder)
  (and
   (q3229352-valid-set-p index-carrier u)
   (q3229352-subset-p index-carrier u index-set)
   (q3229352-countable-set-p index-carrier u)
   (q3229352-disjoint-family-p
    point-carrier index-carrier u family)
   (q3229352-indexed-union-set-p
    point-carrier index-carrier u family union)
   (q3229352-difference-set-p
    point-carrier s union remainder)
   (equal
    (q3229352-measure-value measure remainder)
    (q3229352-ennreal-zero real))))

(defun-sk q3229352-covering-conclusion-p
    (real point-carrier index-carrier measure
     s index-set family)
  (exists (u union remainder)
    (q3229352-covering-conclusion-data-p
     real point-carrier index-carrier measure
     s index-set family u union remainder)))

(defun-sk
    thousand-theorems-q3229352-vitali-covering-theorem-statement ()
  (forall
    (real point-carrier index-carrier distance measurable measure
     s index-set coefficient radius center family)
    (implies
     (and
      (q3229352-real-field-p real)
      (q3229352-set-extensionality-p point-carrier)
      (q3229352-set-extensionality-p index-carrier)
      (q3229352-pseudometric-laws-p
       real point-carrier distance)
      (q3229352-closed-ball-operation-p
       real point-carrier distance)
      (q3229352-second-countable-p
       real point-carrier distance)
      (q3229352-measure-space-p
       real point-carrier measurable measure)
      (q3229352-opens-measurable-p
       real point-carrier distance measurable)
      (q3229352-locally-finite-measure-p
       real point-carrier distance measure)
      (q3229352-valid-set-p point-carrier s)
      (q3229352-valid-set-p index-carrier index-set)
      (q3229352-r-member-p real coefficient)
      (q3229352-r-leq
       real (q3229352-r-zero real) coefficient)
      (q3229352-real-valued-function-p
       real index-carrier radius)
      (q3229352-carrier-valued-function-p
       index-carrier point-carrier center)
      (q3229352-set-valued-family-p
       index-carrier point-carrier family)
      (q3229352-contained-in-indexed-ball-p
       real point-carrier index-carrier distance
       index-set radius center family)
      (q3229352-measure-ball-bound-p
       real point-carrier index-carrier distance measure
       index-set coefficient radius center family)
      (q3229352-family-interiors-nonempty-p
       real point-carrier index-carrier distance index-set family)
      (q3229352-family-closed-p
       real point-carrier index-carrier distance index-set family)
      (q3229352-fine-family-on-set-p
       real point-carrier index-carrier
       s index-set radius center))
     (q3229352-covering-conclusion-p
      real point-carrier index-carrier measure
      s index-set family))))

(value-triple :itpeval-statement-checked)
:q
