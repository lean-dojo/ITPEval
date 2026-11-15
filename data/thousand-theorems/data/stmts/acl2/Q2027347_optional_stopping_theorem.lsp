;; Statement-only formalization of thousand-theorems corpus artifact Q2027347,
;; "Optional stopping theorem": a strongly adapted integrable real-valued
;; process is a submartingale if and only if its stopped-value expectations
;; are monotone for every ordered pair of stopping times whose later member
;; is uniformly bounded. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces give identifiers to arbitrary carriers, subsets,
;; functions, and sequences.  No carrier or function is replaced by a finite
;; table or restricted to an APPLY$ class.  The hypotheses below characterize
;; the real field, sigma algebra, measure, lower integral, real integral,
;; almost-everywhere predicates, and Bochner integration exactly.  Every
;; unbounded quantifier below is a direct DEFUN-SK binder.

;; Real numbers and arbitrary mathematical objects.

(defstub q2027347-r-member-p (real value) t)
(defstub q2027347-r-zero (real) t)
(defstub q2027347-r-one (real) t)
(defstub q2027347-r-add (real left right) t)
(defstub q2027347-r-multiply (real left right) t)
(defstub q2027347-r-negate (real value) t)
(defstub q2027347-r-inverse (real value) t)
(defstub q2027347-r-less (real left right) t)
(defstub q2027347-r-set-member-p (real set value) t)

(defstub q2027347-domain-member-p (domain value) t)
(defstub q2027347-set-member-p (set value) t)
(defstub q2027347-function-value (function argument) t)
(defstub q2027347-function-sequence-value (sequence index) t)
(defstub q2027347-set-sequence-value (sequence index) t)
(defstub q2027347-measurable-set-p (measurable set) t)
(defstub q2027347-measure-value (measure set) t)
(defstub q2027347-lintegral-value
  (lintegral domain measurable measure function) t)
(defstub q2027347-integral-value
  (integral real domain measurable measure lintegral function) t)

(defun q2027347-r-leq (real left right)
  (not (q2027347-r-less real right left)))

(defun q2027347-r-abs (real value)
  (if (q2027347-r-less real value (q2027347-r-zero real))
      (q2027347-r-negate real value)
    value))

(defun-sk q2027347-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2027347-r-member-p real x)
      (q2027347-r-member-p real y)
      (q2027347-r-member-p real z))
     (let* ((zero (q2027347-r-zero real))
            (one (q2027347-r-one real))
            (xy-add (q2027347-r-add real x y))
            (yz-add (q2027347-r-add real y z))
            (xy-mul (q2027347-r-multiply real x y))
            (yz-mul (q2027347-r-multiply real y z))
            (neg-x (q2027347-r-negate real x))
            (inv-x (q2027347-r-inverse real x)))
       (and
        (q2027347-r-member-p real xy-add)
        (q2027347-r-member-p real xy-mul)
        (q2027347-r-member-p real neg-x)
        (q2027347-r-member-p real inv-x)
        (equal
         (q2027347-r-add real xy-add z)
         (q2027347-r-add real x yz-add))
        (equal xy-add (q2027347-r-add real y x))
        (equal (q2027347-r-add real x zero) x)
        (equal (q2027347-r-add real x neg-x) zero)
        (equal
         (q2027347-r-multiply real xy-mul z)
         (q2027347-r-multiply real x yz-mul))
        (equal xy-mul (q2027347-r-multiply real y x))
        (equal (q2027347-r-multiply real x one) x)
        (equal (q2027347-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q2027347-r-multiply real x inv-x)
          one))
        (equal
         (q2027347-r-multiply
          real x (q2027347-r-add real y z))
         (q2027347-r-add
          real
          (q2027347-r-multiply real x y)
          (q2027347-r-multiply real x z))))))))

(defun-sk q2027347-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2027347-r-member-p real x)
      (q2027347-r-member-p real y)
      (q2027347-r-member-p real z))
     (let ((zero (q2027347-r-zero real)))
       (and
        (not (q2027347-r-less real x x))
        (or
         (equal x y)
         (q2027347-r-less real x y)
         (q2027347-r-less real y x))
        (implies
         (and
          (q2027347-r-less real x y)
          (q2027347-r-less real y z))
         (q2027347-r-less real x z))
        (implies
         (q2027347-r-less real x y)
         (q2027347-r-less
          real
          (q2027347-r-add real x z)
          (q2027347-r-add real y z)))
        (implies
         (and
          (q2027347-r-less real zero x)
          (q2027347-r-less real zero y))
         (q2027347-r-less
          real zero
          (q2027347-r-multiply real x y))))))))

(defun-sk q2027347-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q2027347-r-member-p real x)
     (q2027347-r-set-member-p real set x))))

(defun-sk q2027347-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q2027347-r-member-p real x)
      (q2027347-r-set-member-p real set x))
     (q2027347-r-leq real x bound))))

(defun-sk q2027347-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q2027347-r-member-p real bound)
     (q2027347-r-upper-bound-p real set bound))))

(defun-sk q2027347-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q2027347-r-member-p real supremum)
     (q2027347-r-upper-bound-p real set supremum)
     (implies
      (and
       (q2027347-r-member-p real bound)
       (q2027347-r-upper-bound-p real set bound))
      (q2027347-r-leq real supremum bound)))))

(defun-sk q2027347-r-has-supremum-p (real set)
  (exists (supremum)
    (q2027347-r-supremum-p real set supremum)))

(defun-sk q2027347-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q2027347-r-set-nonempty-p real set)
      (q2027347-r-bounded-above-p real set))
     (q2027347-r-has-supremum-p real set))))

(defun q2027347-real-field-p (real)
  (let ((zero (q2027347-r-zero real))
        (one (q2027347-r-one real)))
    (and
     (q2027347-r-member-p real zero)
     (q2027347-r-member-p real one)
     (not (equal zero one))
     (q2027347-r-field-laws-p real)
     (q2027347-r-order-laws-p real)
     (q2027347-r-less real zero one)
     (q2027347-r-dedekind-complete-p real))))

;; Extended nonnegative reals.

(defun q2027347-ennreal-p (real value)
  (or
   (equal value :q2027347-top)
   (and
    (consp value)
    (equal (car value) :q2027347-finite)
    (q2027347-r-member-p real (cdr value))
    (q2027347-r-leq
     real (q2027347-r-zero real) (cdr value)))))

(defun q2027347-ennreal-finite (value)
  (cons :q2027347-finite value))

(defun q2027347-ennreal-zero (real)
  (q2027347-ennreal-finite (q2027347-r-zero real)))

(defun q2027347-ennreal-less (real left right)
  (cond
   ((equal left :q2027347-top) nil)
   ((equal right :q2027347-top) t)
   (t (q2027347-r-less real (cdr left) (cdr right)))))

(defun q2027347-ennreal-leq (real left right)
  (not (q2027347-ennreal-less real right left)))

(defun q2027347-ennreal-add (real left right)
  (if (or (equal left :q2027347-top)
          (equal right :q2027347-top))
      :q2027347-top
    (q2027347-ennreal-finite
     (q2027347-r-add real (cdr left) (cdr right)))))

(defun q2027347-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q2027347-ennreal-zero real))
        (equal right (q2027347-ennreal-zero real)))
    (q2027347-ennreal-zero real))
   ((or (equal left :q2027347-top)
        (equal right :q2027347-top))
    :q2027347-top)
   (t
    (q2027347-ennreal-finite
     (q2027347-r-multiply real (cdr left) (cdr right))))))

(defun q2027347-ennreal-to-real (real value)
  (if (and (consp value)
           (equal (car value) :q2027347-finite))
      (cdr value)
    (q2027347-r-zero real)))

;; Sets, sigma algebras, and measures.

(defun-sk q2027347-valid-set-p (domain set)
  (forall (x)
    (implies
     (q2027347-set-member-p set x)
     (q2027347-domain-member-p domain x))))

(defun-sk q2027347-set-subset-p (left right)
  (forall (x)
    (implies
     (q2027347-set-member-p left x)
     (q2027347-set-member-p right x))))

(defun-sk q2027347-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (iff
      (q2027347-set-member-p left x)
      (q2027347-set-member-p right x)))))

(defun-sk q2027347-empty-set-p (domain set)
  (forall (x)
    (iff
     (q2027347-set-member-p set x)
     (and (q2027347-domain-member-p domain x) nil))))

(defun-sk q2027347-complement-set-p (domain set complement)
  (forall (x)
    (iff
     (q2027347-set-member-p complement x)
     (and
      (q2027347-domain-member-p domain x)
      (not (q2027347-set-member-p set x))))))

(defun-sk q2027347-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q2027347-valid-set-p
      domain
      (q2027347-set-sequence-value sequence n)))))

(defun-sk q2027347-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q2027347-set-member-p
      (q2027347-set-sequence-value sequence n)
      x))))

(defun-sk q2027347-sequence-union-set-p
    (domain sequence union)
  (forall (x)
    (iff
     (q2027347-set-member-p union x)
     (and
      (q2027347-domain-member-p domain x)
      (q2027347-sequence-union-member-p sequence x)))))

(defun-sk q2027347-family-extensional-p (domain measurable)
  (forall (left right)
    (implies
     (q2027347-set-equiv-p domain left right)
     (iff
      (q2027347-measurable-set-p measurable left)
      (q2027347-measurable-set-p measurable right)))))

(defun-sk q2027347-family-valid-p (domain measurable)
  (forall (set)
    (implies
     (q2027347-measurable-set-p measurable set)
     (q2027347-valid-set-p domain set))))

(defun-sk q2027347-measurable-empty-exists-p (domain measurable)
  (exists (empty)
    (and
     (q2027347-empty-set-p domain empty)
     (q2027347-measurable-set-p measurable empty))))

(defun-sk q2027347-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q2027347-complement-set-p domain set complement)
     (q2027347-measurable-set-p measurable complement))))

(defun-sk q2027347-measurable-complements-p
    (domain measurable)
  (forall (set)
    (implies
     (q2027347-measurable-set-p measurable set)
     (q2027347-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q2027347-sequence-measurable-p (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q2027347-measurable-set-p
      measurable
      (q2027347-set-sequence-value sequence n)))))

(defun-sk q2027347-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q2027347-sequence-union-set-p domain sequence union)
     (q2027347-measurable-set-p measurable union))))

(defun-sk q2027347-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q2027347-set-sequence-p domain sequence)
      (q2027347-sequence-measurable-p measurable sequence))
     (q2027347-measurable-union-exists-p
      domain measurable sequence))))

(defun q2027347-sigma-algebra-p (domain measurable)
  (and
   (q2027347-family-extensional-p domain measurable)
   (q2027347-family-valid-p domain measurable)
   (q2027347-measurable-empty-exists-p domain measurable)
   (q2027347-measurable-complements-p domain measurable)
   (q2027347-measurable-sequence-unions-p domain measurable)))

(defun-sk q2027347-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q2027347-set-member-p left x)
      (q2027347-set-member-p right x)))))

(defun-sk q2027347-pairwise-disjoint-p (sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (q2027347-disjoint-sets-p
      (q2027347-set-sequence-value sequence m)
      (q2027347-set-sequence-value sequence n)))))

(defun q2027347-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q2027347-ennreal-zero real)
    (q2027347-ennreal-add
     real
     (q2027347-measure-prefix-sum
      real measure sequence (1- count))
     (q2027347-measure-value
      measure
      (q2027347-set-sequence-value sequence (1- count))))))

(defun-sk q2027347-countable-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q2027347-ennreal-leq
      real
      (q2027347-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q2027347-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q2027347-ennreal-p real total)
     (q2027347-countable-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q2027347-ennreal-p real bound)
       (q2027347-countable-sum-upper-bound-p
        real measure sequence bound))
      (q2027347-ennreal-leq real total bound)))))

(defun-sk q2027347-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q2027347-set-equiv-p domain left right)
     (equal
      (q2027347-measure-value measure left)
      (q2027347-measure-value measure right)))))

(defun-sk q2027347-measure-values-p (real domain measure)
  (forall (set)
    (implies
     (q2027347-valid-set-p domain set)
     (q2027347-ennreal-p
      real (q2027347-measure-value measure set)))))

(defun-sk q2027347-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q2027347-empty-set-p domain empty)
     (equal
      (q2027347-measure-value measure empty)
      (q2027347-ennreal-zero real)))))

(defun-sk q2027347-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q2027347-set-sequence-p domain sequence)
      (q2027347-sequence-measurable-p measurable sequence)
      (q2027347-pairwise-disjoint-p sequence)
      (q2027347-sequence-union-set-p domain sequence union))
     (q2027347-countable-sum-p
      real measure sequence
      (q2027347-measure-value measure union)))))

(defun-sk q2027347-measurable-superset-lower-bound-p
    (real measurable measure set lower)
  (forall (superset)
    (implies
     (and
      (q2027347-measurable-set-p measurable superset)
      (q2027347-set-subset-p set superset))
     (q2027347-ennreal-leq
      real lower
      (q2027347-measure-value measure superset)))))

(defun-sk q2027347-outer-measure-value-p
    (real measurable measure set)
  (forall (lower)
    (and
     (q2027347-measurable-superset-lower-bound-p
      real measurable measure set
      (q2027347-measure-value measure set))
     (implies
      (and
       (q2027347-ennreal-p real lower)
       (q2027347-measurable-superset-lower-bound-p
        real measurable measure set lower))
      (q2027347-ennreal-leq
       real lower
       (q2027347-measure-value measure set))))))

(defun-sk q2027347-outer-measure-values-p
    (real domain measurable measure)
  (forall (set)
    (implies
     (q2027347-valid-set-p domain set)
     (q2027347-outer-measure-value-p
      real measurable measure set))))

(defun q2027347-measure-space-p
    (real domain measurable measure)
  (and
   (q2027347-sigma-algebra-p domain measurable)
   (q2027347-measure-extensional-p domain measure)
   (q2027347-measure-values-p real domain measure)
   (q2027347-measure-empty-zero-p real domain measure)
   (q2027347-countably-additive-p
    real domain measurable measure)
   (q2027347-outer-measure-values-p
    real domain measurable measure)))

(defun q2027347-null-set-p (real domain measure set)
  (and
   (q2027347-valid-set-p domain set)
   (equal
    (q2027347-measure-value measure set)
    (q2027347-ennreal-zero real))))

;; Typed functions and measurability through upper-ray preimages.

(defun-sk q2027347-real-function-p (real domain function)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (q2027347-r-member-p
      real (q2027347-function-value function x)))))

(defun-sk q2027347-ennreal-function-p (real domain function)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (q2027347-ennreal-p
      real (q2027347-function-value function x)))))

(defun-sk q2027347-real-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q2027347-set-member-p set x)
     (and
      (q2027347-domain-member-p domain x)
      (q2027347-r-less
       real threshold
       (q2027347-function-value function x))))))

(defun-sk q2027347-ennreal-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q2027347-set-member-p set x)
     (and
      (q2027347-domain-member-p domain x)
      (q2027347-ennreal-less
       real threshold
       (q2027347-function-value function x))))))

(defun-sk q2027347-real-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q2027347-real-upper-preimage-set-p
      real domain function threshold set)
     (q2027347-measurable-set-p measurable set))))

(defun-sk q2027347-ennreal-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q2027347-ennreal-upper-preimage-set-p
      real domain function threshold set)
     (q2027347-measurable-set-p measurable set))))

(defun-sk q2027347-measurable-real-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q2027347-real-function-p real domain function)
     (implies
      (q2027347-r-member-p real threshold)
      (q2027347-real-upper-preimage-exists-p
       real domain measurable function threshold)))))

(defun-sk q2027347-measurable-ennreal-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q2027347-ennreal-function-p real domain function)
     (implies
      (q2027347-ennreal-p real threshold)
      (q2027347-ennreal-upper-preimage-exists-p
       real domain measurable function threshold)))))

(defun-sk q2027347-disagreement-set-p
    (domain left right set)
  (forall (x)
    (iff
     (q2027347-set-member-p set x)
     (and
      (q2027347-domain-member-p domain x)
      (not
       (equal
        (q2027347-function-value left x)
        (q2027347-function-value right x)))))))

(defun-sk q2027347-ae-equal-p
    (real domain measure left right)
  (exists (set)
    (and
     (q2027347-disagreement-set-p domain left right set)
     (q2027347-null-set-p real domain measure set))))

(defun-sk q2027347-ae-real-measurable-p
    (real domain measurable measure function)
  (exists (representative)
    (and
     (q2027347-real-function-p real domain function)
     (q2027347-measurable-real-function-p
      real domain measurable representative)
     (q2027347-ae-equal-p
      real domain measure function representative))))

(defun-sk q2027347-ae-ennreal-measurable-p
    (real domain measurable measure function)
  (exists (representative)
    (and
     (q2027347-ennreal-function-p real domain function)
     (q2027347-measurable-ennreal-function-p
      real domain measurable representative)
     (q2027347-ae-equal-p
      real domain measure function representative))))

;; The lower Lebesgue integral as the supremum of measurable finite-range
;; simple functions below the integrand.

(defun-sk q2027347-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q2027347-domain-member-p domain x)
     (equal
      (q2027347-function-value function x)
      value))))

(defun q2027347-values-attained-p
    (domain function values)
  (if (consp values)
      (and
       (q2027347-value-attained-p
        domain function (car values))
       (q2027347-values-attained-p
        domain function (cdr values)))
    (equal values nil)))

(defun q2027347-ennreal-value-list-p (real values)
  (if (consp values)
      (and
       (q2027347-ennreal-p real (car values))
       (q2027347-ennreal-value-list-p real (cdr values)))
    (equal values nil)))

(defun-sk q2027347-range-in-values-p
    (domain function values)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (member-equal
      (q2027347-function-value function x)
      values))))

(defun-sk q2027347-fiber-set-p
    (domain function value set)
  (forall (x)
    (iff
     (q2027347-set-member-p set x)
     (and
      (q2027347-domain-member-p domain x)
      (equal
       (q2027347-function-value function x)
       value)))))

(defun q2027347-fiber-list-p
    (domain function values fibers)
  (if (consp values)
      (and
       (consp fibers)
       (q2027347-fiber-set-p
        domain function (car values) (car fibers))
       (q2027347-fiber-list-p
        domain function (cdr values) (cdr fibers)))
    (equal fibers nil)))

(defun q2027347-finite-simple-integral
    (real measure values fibers)
  (if (consp values)
      (q2027347-ennreal-add
       real
       (q2027347-ennreal-multiply
        real
        (car values)
        (q2027347-measure-value measure (car fibers)))
       (q2027347-finite-simple-integral
        real measure (cdr values) (cdr fibers)))
    (q2027347-ennreal-zero real)))

(defun q2027347-simple-function-data-p
    (real domain measurable function values fibers)
  (and
   (true-listp values)
   (true-listp fibers)
   (no-duplicatesp-equal values)
   (q2027347-ennreal-value-list-p real values)
   (q2027347-values-attained-p domain function values)
   (q2027347-range-in-values-p domain function values)
   (q2027347-fiber-list-p domain function values fibers)
   (q2027347-measurable-ennreal-function-p
    real domain measurable function)))

(defun-sk q2027347-simple-below-p
    (real domain simple function)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (q2027347-ennreal-leq
      real
      (q2027347-function-value simple x)
      (q2027347-function-value function x)))))

(defun-sk q2027347-lintegral-upper-bound-p
    (real domain measurable measure function bound)
  (forall (simple values fibers)
    (implies
     (and
      (q2027347-simple-function-data-p
       real domain measurable simple values fibers)
      (q2027347-simple-below-p
       real domain simple function))
     (q2027347-ennreal-leq
      real
      (q2027347-finite-simple-integral
       real measure values fibers)
      bound))))

(defun-sk q2027347-lintegral-value-p
    (real domain measurable measure function value)
  (forall (bound)
    (and
     (q2027347-ennreal-function-p real domain function)
     (q2027347-ennreal-p real value)
     (q2027347-lintegral-upper-bound-p
      real domain measurable measure function value)
     (implies
      (and
       (q2027347-ennreal-p real bound)
       (q2027347-lintegral-upper-bound-p
        real domain measurable measure function bound))
      (q2027347-ennreal-leq real value bound)))))

(defun-sk q2027347-lintegral-operation-p
    (real domain measurable measure lintegral)
  (forall (function)
    (implies
     (q2027347-ennreal-function-p real domain function)
     (q2027347-lintegral-value-p
      real domain measurable measure function
      (q2027347-lintegral-value
       lintegral domain measurable measure function)))))

;; The real Bochner integral, specialized to real-valued functions.

(defun-sk q2027347-enorm-function-p
    (real domain function enorm-function)
  (forall (x)
    (and
     (q2027347-ennreal-function-p real domain enorm-function)
     (implies
      (q2027347-domain-member-p domain x)
      (equal
       (q2027347-function-value enorm-function x)
       (q2027347-ennreal-finite
        (q2027347-r-abs
         real
         (q2027347-function-value function x))))))))

(defun-sk q2027347-integrable-enorm-exists-p
    (real domain measurable measure lintegral function)
  (exists (enorm-function)
    (and
     (q2027347-enorm-function-p
      real domain function enorm-function)
     (q2027347-ennreal-less
      real
      (q2027347-lintegral-value
       lintegral domain measurable measure enorm-function)
      :q2027347-top))))

(defun q2027347-integrable-p
    (real domain measurable measure lintegral function)
  (and
   (q2027347-ae-real-measurable-p
    real domain measurable measure function)
   (q2027347-integrable-enorm-exists-p
    real domain measurable measure lintegral function)))

(defun-sk q2027347-positive-part-function-p
    (real domain function positive)
  (forall (x)
    (and
     (q2027347-ennreal-function-p real domain positive)
     (implies
      (q2027347-domain-member-p domain x)
      (equal
       (q2027347-function-value positive x)
       (q2027347-ennreal-finite
        (if
            (q2027347-r-less
             real
             (q2027347-function-value function x)
             (q2027347-r-zero real))
            (q2027347-r-zero real)
          (q2027347-function-value function x))))))))

(defun-sk q2027347-negative-part-function-p
    (real domain function negative)
  (forall (x)
    (and
     (q2027347-ennreal-function-p real domain negative)
     (implies
      (q2027347-domain-member-p domain x)
      (let ((negated
             (q2027347-r-negate
              real
              (q2027347-function-value function x))))
        (equal
         (q2027347-function-value negative x)
         (q2027347-ennreal-finite
          (if
              (q2027347-r-less
               real negated (q2027347-r-zero real))
              (q2027347-r-zero real)
            negated))))))))

(defun-sk q2027347-real-integral-witness-exists-p
    (integral real domain measurable measure lintegral function value)
  (exists (positive negative)
    (and
     (q2027347-positive-part-function-p
      real domain function positive)
     (q2027347-negative-part-function-p
      real domain function negative)
     (equal
      value
      (q2027347-r-add
       real
       (q2027347-ennreal-to-real
        real
        (q2027347-lintegral-value
         lintegral domain measurable measure positive))
       (q2027347-r-negate
        real
        (q2027347-ennreal-to-real
         real
         (q2027347-lintegral-value
          lintegral domain measurable measure negative))))))))

(defun q2027347-real-integral-value-p
    (integral real domain measurable measure lintegral function value)
  (and
   (q2027347-r-member-p real value)
   (if
       (q2027347-integrable-p
        real domain measurable measure lintegral function)
       (q2027347-real-integral-witness-exists-p
        integral real domain measurable measure
        lintegral function value)
     (equal value (q2027347-r-zero real)))))

(defun-sk q2027347-real-integral-operation-p
    (integral real domain measurable measure lintegral)
  (forall (function)
    (implies
     (q2027347-real-function-p real domain function)
     (q2027347-real-integral-value-p
      integral real domain measurable measure lintegral function
      (q2027347-integral-value
       integral real domain measurable measure
       lintegral function)))))

;; Filtrations and process fibers are represented by conservative object
;; constructors.  Their pointwise meanings are imposed by direct quantified
;; laws, rather than generated function terms.

(defstub q2027347-filtration-level (filtration index) t)
(defstub q2027347-process-fiber (process index) t)
(defstub q2027347-restricted-function (set function zero) t)
(defstub q2027347-stopping-level-set
  (domain stopping-time index) t)
(defstub q2027347-stopped-function
  (stopping-time process zero) t)

(defun-sk q2027347-process-fiber-operation-p ()
  (forall (process n x)
    (equal
     (q2027347-function-value
      (q2027347-process-fiber process n) x)
     (q2027347-function-value process (cons n x)))))

(defun-sk q2027347-restricted-function-operation-p (real)
  (forall (set function x)
    (equal
     (q2027347-function-value
      (q2027347-restricted-function
       set function (q2027347-r-zero real))
      x)
     (if (q2027347-set-member-p set x)
         (q2027347-function-value function x)
       (q2027347-r-zero real)))))

;; Sigma-finite filtrations.

(defun-sk q2027347-filtration-levels-p (domain filtration)
  (forall (n)
    (implies
     (natp n)
     (q2027347-sigma-algebra-p
      domain (q2027347-filtration-level filtration n)))))

(defun-sk q2027347-filtration-contained-p
    (measurable filtration)
  (forall (n set)
    (implies
     (and
      (natp n)
      (q2027347-measurable-set-p
       (q2027347-filtration-level filtration n) set))
     (q2027347-measurable-set-p measurable set))))

(defun-sk q2027347-filtration-monotone-p (filtration)
  (forall (i j set)
    (implies
     (and
      (natp i)
      (natp j)
      (<= i j)
      (q2027347-measurable-set-p
       (q2027347-filtration-level filtration i) set))
     (q2027347-measurable-set-p
      (q2027347-filtration-level filtration j) set))))

(defun q2027347-filtration-p
    (domain measurable filtration)
  (and
   (q2027347-filtration-levels-p domain filtration)
   (q2027347-filtration-contained-p measurable filtration)
   (q2027347-filtration-monotone-p filtration)))

(defun-sk q2027347-sigma-cover-levels-p
    (real measurable measure sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((set (q2027347-set-sequence-value sequence n)))
       (and
        (q2027347-measurable-set-p measurable set)
        (not
         (equal
          (q2027347-measure-value measure set)
          :q2027347-top)))))))

(defun-sk q2027347-sigma-cover-index-exists-p
    (sequence x)
  (exists (n)
    (and
     (natp n)
     (q2027347-set-member-p
      (q2027347-set-sequence-value sequence n) x))))

(defun-sk q2027347-sigma-cover-covers-p
    (domain sequence)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (q2027347-sigma-cover-index-exists-p sequence x))))

(defun q2027347-sigma-finite-cover-p
    (real domain measurable measure sequence)
  (and
   (q2027347-set-sequence-p domain sequence)
   (q2027347-sigma-cover-levels-p
    real measurable measure sequence)
   (q2027347-sigma-cover-covers-p domain sequence)))

(defun-sk q2027347-sigma-finite-p
    (real domain measurable measure)
  (exists (sequence)
    (q2027347-sigma-finite-cover-p
     real domain measurable measure sequence)))

(defun-sk q2027347-filtration-level-sigma-finite-p
    (real domain measure filtration n)
  (exists (sequence)
    (q2027347-sigma-finite-cover-p
     real domain
     (q2027347-filtration-level filtration n)
     measure sequence)))

(defun-sk q2027347-sigma-finite-filtration-p
    (real domain measure filtration)
  (forall (n)
    (implies
     (natp n)
     (q2027347-filtration-level-sigma-finite-p
      real domain measure filtration n))))

;; Strong adaptation and integrability of the real-valued process.

(defun-sk q2027347-real-process-p
    (real domain process)
  (forall (n)
    (implies
     (natp n)
     (q2027347-real-function-p
      real domain (q2027347-process-fiber process n)))))

(defun-sk q2027347-strongly-adapted-p
    (real domain filtration process)
  (forall (n)
    (implies
     (natp n)
     (q2027347-measurable-real-function-p
      real domain
      (q2027347-filtration-level filtration n)
      (q2027347-process-fiber process n)))))

(defun-sk q2027347-process-integrable-p
    (real domain measurable measure lintegral process)
  (forall (n)
    (implies
     (natp n)
     (q2027347-integrable-p
      real domain measurable measure lintegral
      (q2027347-process-fiber process n)))))

(defun q2027347-process-context-p
    (real domain measurable measure lintegral filtration process)
  (and
   (q2027347-real-process-p real domain process)
   (q2027347-strongly-adapted-p
    real domain filtration process)
   (q2027347-process-integrable-p
    real domain measurable measure lintegral process)))

;; The submartingale predicate uses the equivalent set-integral
;; characterization: for i <= j and every set measurable at time i, the
;; integral of f_i over that set is at most the integral of f_j.

(defun q2027347-set-integral-value
    (integral real domain measurable measure lintegral
     function set)
  (q2027347-integral-value
   integral real domain measurable measure lintegral
   (q2027347-restricted-function
    set function (q2027347-r-zero real))))

(defun-sk q2027347-submartingale-set-integrals-p
    (integral real domain measurable measure lintegral
     filtration process)
  (forall (i j set)
    (implies
     (and
      (natp i)
      (natp j)
      (<= i j)
      (q2027347-measurable-set-p
       (q2027347-filtration-level filtration i) set))
     (q2027347-r-leq
      real
      (q2027347-set-integral-value
       integral real domain measurable measure lintegral
       (q2027347-process-fiber process i) set)
      (q2027347-set-integral-value
       integral real domain measurable measure lintegral
       (q2027347-process-fiber process j) set)))))

(defun q2027347-submartingale-p
    (integral real domain measurable measure lintegral
     filtration process)
  (and
   (q2027347-process-context-p
    real domain measurable measure lintegral filtration process)
   (q2027347-submartingale-set-integrals-p
    integral real domain measurable measure lintegral
    filtration process)))

;; Stopping times Ω -> ℕ∞, including the top value.

(defun q2027347-extended-natural-p (value)
  (or (natp value)
      (equal value :q2027347-nat-top)))

(defun q2027347-extended-natural-leq (left right)
  (if (equal right :q2027347-nat-top)
      (q2027347-extended-natural-p left)
    (and
     (natp left)
     (natp right)
     (<= left right))))

(defun-sk q2027347-stopping-values-p
    (domain stopping-time)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (q2027347-extended-natural-p
      (q2027347-function-value stopping-time x)))))

(defun-sk q2027347-stopping-level-set-operation-p
    (domain)
  (forall (stopping-time n x)
    (iff
     (q2027347-set-member-p
      (q2027347-stopping-level-set
       domain stopping-time n)
      x)
     (and
      (q2027347-domain-member-p domain x)
      (q2027347-extended-natural-leq
       (q2027347-function-value stopping-time x)
       n)))))

(defun-sk q2027347-stopping-levels-measurable-p
    (domain filtration stopping-time)
  (forall (n)
    (implies
     (natp n)
     (q2027347-measurable-set-p
      (q2027347-filtration-level filtration n)
      (q2027347-stopping-level-set
       domain stopping-time n)))))

(defun q2027347-stopping-time-p
    (domain filtration stopping-time)
  (and
   (q2027347-stopping-values-p domain stopping-time)
   (q2027347-stopping-levels-measurable-p
    domain filtration stopping-time)))

(defun-sk q2027347-stopping-times-ordered-p
    (domain left right)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (q2027347-extended-natural-leq
      (q2027347-function-value left x)
      (q2027347-function-value right x)))))

(defun-sk q2027347-stopping-time-bounded-by-p
    (domain stopping-time bound)
  (forall (x)
    (implies
     (q2027347-domain-member-p domain x)
     (q2027347-extended-natural-leq
      (q2027347-function-value stopping-time x)
      bound))))

(defun-sk q2027347-bounded-stopping-time-p
    (domain stopping-time)
  (exists (bound)
    (and
     (natp bound)
     (q2027347-stopping-time-bounded-by-p
      domain stopping-time bound))))

;; stoppedValue f τ is f (τ x) x when τ x is finite and zero at top.

(defun-sk q2027347-stopped-function-operation-p
    (real)
  (forall (stopping-time process x)
    (let ((time
           (q2027347-function-value stopping-time x)))
      (equal
       (q2027347-function-value
        (q2027347-stopped-function
         stopping-time process (q2027347-r-zero real))
        x)
       (if
           (natp time)
           (q2027347-function-value
            (q2027347-process-fiber process time) x)
         (q2027347-r-zero real))))))

(defun q2027347-expectation
    (integral real domain measurable measure lintegral
     stopping-time process)
  (q2027347-integral-value
   integral real domain measurable measure lintegral
   (q2027347-stopped-function
    stopping-time process (q2027347-r-zero real))))

;; This is exactly the right-hand side of the Lean biconditional.  In
;; particular, the bound is an internal existential witness depending on π.

(defun-sk q2027347-optional-stopping-monotonicity-p
    (integral real domain measurable measure lintegral
     filtration process)
  (forall (tau pi-time)
    (implies
     (and
      (q2027347-stopping-time-p domain filtration tau)
      (q2027347-stopping-time-p domain filtration pi-time)
      (q2027347-stopping-times-ordered-p domain tau pi-time)
      (q2027347-bounded-stopping-time-p domain pi-time))
     (q2027347-r-leq
      real
      (q2027347-expectation
       integral real domain measurable measure lintegral
       tau process)
      (q2027347-expectation
       integral real domain measurable measure lintegral
       pi-time process)))))

(defun-sk
    thousand-theorems-q2027347-optional-stopping-theorem-statement
    ()
  (forall
      (integral real domain measurable measure lintegral
       filtration process)
    (implies
     (and
      (q2027347-real-field-p real)
      (q2027347-measure-space-p
       real domain measurable measure)
      (q2027347-lintegral-operation-p
       real domain measurable measure lintegral)
      (q2027347-real-integral-operation-p
       integral real domain measurable measure lintegral)
      (q2027347-filtration-p domain measurable filtration)
      (q2027347-sigma-finite-filtration-p
       real domain measure filtration)
      (q2027347-process-fiber-operation-p)
      (q2027347-restricted-function-operation-p real)
      (q2027347-stopping-level-set-operation-p domain)
      (q2027347-stopped-function-operation-p real)
      (q2027347-process-context-p
       real domain measurable measure lintegral
       filtration process))
     (iff
      (q2027347-submartingale-p
       integral real domain measurable measure lintegral
       filtration process)
      (q2027347-optional-stopping-monotonicity-p
       integral real domain measurable measure lintegral
       filtration process)))))

(value-triple :itpeval-statement-checked)
:q
