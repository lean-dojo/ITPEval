;; Statement-only formalization of thousand-theorems corpus artifact Q643826,
;; "Slutsky's theorem": a continuous function of random variables converging
;; respectively in distribution and in probability to a constant converges
;; in distribution to the corresponding continuous image. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces give identifiers to arbitrary carriers, subsets,
;; functions, and sequences.  No carrier or function is replaced by a finite
;; table or restricted to an APPLY$ class.  The hypotheses below characterize
;; the real field, topological and measurable spaces, probability measures,
;; Lebesgue integrals, filters, almost-everywhere measurability, convergence
;; in measure, and weak convergence of laws explicitly.

;; Real numbers and arbitrary mathematical objects.

(defstub q643826-r-member-p (real value) t)
(defstub q643826-r-zero (real) t)
(defstub q643826-r-one (real) t)
(defstub q643826-r-add (real left right) t)
(defstub q643826-r-multiply (real left right) t)
(defstub q643826-r-negate (real value) t)
(defstub q643826-r-inverse (real value) t)
(defstub q643826-r-less (real left right) t)
(defstub q643826-r-set-member-p (real set value) t)

(defstub q643826-domain-member-p (domain value) t)
(defstub q643826-set-member-p (set value) t)
(defstub q643826-function-value (function argument) t)
(defstub q643826-function2-value (function left right) t)
(defstub q643826-function-sequence-value (sequence index) t)
(defstub q643826-set-sequence-value (sequence index) t)
(defstub q643826-measurable-set-p (measurable set) t)
(defstub q643826-measure-value (measure set) t)
(defstub q643826-open-set-p (topology set) t)
(defstub q643826-filter-set-p (filter set) t)
(defstub q643826-set-family-member-p (family set) t)
(defstub q643826-object-zero (zero-operation) t)
(defstub q643826-object-add (add-operation left right) t)
(defstub q643826-object-negate (negate-operation value) t)
(defstub q643826-norm-value (norm-operation real value) t)
(defstub q643826-lintegral-value
  (lintegral domain measurable measure function) t)
(defstub q643826-integral-value
  (integral real domain measurable measure lintegral function) t)

(defun q643826-r-leq (real left right)
  (not (q643826-r-less real right left)))

(defun q643826-r-abs (real value)
  (if (q643826-r-less real value (q643826-r-zero real))
      (q643826-r-negate real value)
    value))

(defun-sk q643826-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q643826-r-member-p real x)
      (q643826-r-member-p real y)
      (q643826-r-member-p real z))
     (let* ((zero (q643826-r-zero real))
            (one (q643826-r-one real))
            (xy-add (q643826-r-add real x y))
            (yz-add (q643826-r-add real y z))
            (xy-mul (q643826-r-multiply real x y))
            (yz-mul (q643826-r-multiply real y z))
            (neg-x (q643826-r-negate real x))
            (inv-x (q643826-r-inverse real x)))
       (and
        (q643826-r-member-p real xy-add)
        (q643826-r-member-p real xy-mul)
        (q643826-r-member-p real neg-x)
        (q643826-r-member-p real inv-x)
        (equal
         (q643826-r-add real xy-add z)
         (q643826-r-add real x yz-add))
        (equal xy-add (q643826-r-add real y x))
        (equal (q643826-r-add real x zero) x)
        (equal (q643826-r-add real x neg-x) zero)
        (equal
         (q643826-r-multiply real xy-mul z)
         (q643826-r-multiply real x yz-mul))
        (equal xy-mul (q643826-r-multiply real y x))
        (equal (q643826-r-multiply real x one) x)
        (equal (q643826-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q643826-r-multiply real x inv-x)
          one))
        (equal
         (q643826-r-multiply
          real x (q643826-r-add real y z))
         (q643826-r-add
          real
          (q643826-r-multiply real x y)
          (q643826-r-multiply real x z))))))))

(defun-sk q643826-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q643826-r-member-p real x)
      (q643826-r-member-p real y)
      (q643826-r-member-p real z))
     (let ((zero (q643826-r-zero real)))
       (and
        (not (q643826-r-less real x x))
        (or
         (equal x y)
         (q643826-r-less real x y)
         (q643826-r-less real y x))
        (implies
         (and
          (q643826-r-less real x y)
          (q643826-r-less real y z))
         (q643826-r-less real x z))
        (implies
         (q643826-r-less real x y)
         (q643826-r-less
          real
          (q643826-r-add real x z)
          (q643826-r-add real y z)))
        (implies
         (and
          (q643826-r-less real zero x)
          (q643826-r-less real zero y))
         (q643826-r-less
          real zero
          (q643826-r-multiply real x y))))))))

(defun-sk q643826-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q643826-r-member-p real x)
     (q643826-r-set-member-p real set x))))

(defun-sk q643826-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q643826-r-member-p real x)
      (q643826-r-set-member-p real set x))
     (q643826-r-leq real x bound))))

(defun-sk q643826-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q643826-r-member-p real bound)
     (q643826-r-upper-bound-p real set bound))))

(defun-sk q643826-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q643826-r-member-p real supremum)
     (q643826-r-upper-bound-p real set supremum)
     (implies
      (and
       (q643826-r-member-p real bound)
       (q643826-r-upper-bound-p real set bound))
      (q643826-r-leq real supremum bound)))))

(defun-sk q643826-r-has-supremum-p (real set)
  (exists (supremum)
    (q643826-r-supremum-p real set supremum)))

(defun-sk q643826-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q643826-r-set-nonempty-p real set)
      (q643826-r-bounded-above-p real set))
     (q643826-r-has-supremum-p real set))))

(defun q643826-real-field-p (real)
  (let ((zero (q643826-r-zero real))
        (one (q643826-r-one real)))
    (and
     (q643826-r-member-p real zero)
     (q643826-r-member-p real one)
     (not (equal zero one))
     (q643826-r-field-laws-p real)
     (q643826-r-order-laws-p real)
     (q643826-r-less real zero one)
     (q643826-r-dedekind-complete-p real))))

;; Extended nonnegative reals.

(defun q643826-ennreal-p (real value)
  (or
   (equal value :q643826-top)
   (and
    (consp value)
    (equal (car value) :q643826-finite)
    (q643826-r-member-p real (cdr value))
    (q643826-r-leq
     real (q643826-r-zero real) (cdr value)))))

(defun q643826-ennreal-finite (value)
  (cons :q643826-finite value))

(defun q643826-ennreal-zero (real)
  (q643826-ennreal-finite (q643826-r-zero real)))

(defun q643826-ennreal-less (real left right)
  (cond
   ((equal left :q643826-top) nil)
   ((equal right :q643826-top) t)
   (t (q643826-r-less real (cdr left) (cdr right)))))

(defun q643826-ennreal-leq (real left right)
  (not (q643826-ennreal-less real right left)))

(defun q643826-ennreal-add (real left right)
  (if (or (equal left :q643826-top)
          (equal right :q643826-top))
      :q643826-top
    (q643826-ennreal-finite
     (q643826-r-add real (cdr left) (cdr right)))))

(defun q643826-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q643826-ennreal-zero real))
        (equal right (q643826-ennreal-zero real)))
    (q643826-ennreal-zero real))
   ((or (equal left :q643826-top)
        (equal right :q643826-top))
    :q643826-top)
   (t
    (q643826-ennreal-finite
     (q643826-r-multiply real (cdr left) (cdr right))))))

(defun q643826-ennreal-to-real (real value)
  (if (and (consp value)
           (equal (car value) :q643826-finite))
      (cdr value)
    (q643826-r-zero real)))

;; Sets, sigma algebras, and measures.

(defun-sk q643826-valid-set-p (domain set)
  (forall (x)
    (implies
     (q643826-set-member-p set x)
     (q643826-domain-member-p domain x))))

(defun-sk q643826-set-subset-p (left right)
  (forall (x)
    (implies
     (q643826-set-member-p left x)
     (q643826-set-member-p right x))))

(defun-sk q643826-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q643826-domain-member-p domain x)
     (iff
      (q643826-set-member-p left x)
      (q643826-set-member-p right x)))))

(defun-sk q643826-empty-set-p (domain set)
  (forall (x)
    (iff
     (q643826-set-member-p set x)
     (and (q643826-domain-member-p domain x) nil))))

(defun-sk q643826-complement-set-p (domain set complement)
  (forall (x)
    (iff
     (q643826-set-member-p complement x)
     (and
      (q643826-domain-member-p domain x)
      (not (q643826-set-member-p set x))))))

(defun-sk q643826-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q643826-valid-set-p
      domain
      (q643826-set-sequence-value sequence n)))))

(defun-sk q643826-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q643826-set-member-p
      (q643826-set-sequence-value sequence n)
      x))))

(defun-sk q643826-sequence-union-set-p
    (domain sequence union)
  (forall (x)
    (iff
     (q643826-set-member-p union x)
     (and
      (q643826-domain-member-p domain x)
      (q643826-sequence-union-member-p sequence x)))))

(defun-sk q643826-family-extensional-p (domain measurable)
  (forall (left right)
    (implies
     (q643826-set-equiv-p domain left right)
     (iff
      (q643826-measurable-set-p measurable left)
      (q643826-measurable-set-p measurable right)))))

(defun-sk q643826-family-valid-p (domain measurable)
  (forall (set)
    (implies
     (q643826-measurable-set-p measurable set)
     (q643826-valid-set-p domain set))))

(defun-sk q643826-measurable-empty-exists-p (domain measurable)
  (exists (empty)
    (and
     (q643826-empty-set-p domain empty)
     (q643826-measurable-set-p measurable empty))))

(defun-sk q643826-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q643826-complement-set-p domain set complement)
     (q643826-measurable-set-p measurable complement))))

(defun-sk q643826-measurable-complements-p
    (domain measurable)
  (forall (set)
    (implies
     (q643826-measurable-set-p measurable set)
     (q643826-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q643826-sequence-measurable-p (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q643826-measurable-set-p
      measurable
      (q643826-set-sequence-value sequence n)))))

(defun-sk q643826-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q643826-sequence-union-set-p domain sequence union)
     (q643826-measurable-set-p measurable union))))

(defun-sk q643826-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q643826-set-sequence-p domain sequence)
      (q643826-sequence-measurable-p measurable sequence))
     (q643826-measurable-union-exists-p
      domain measurable sequence))))

(defun q643826-sigma-algebra-p (domain measurable)
  (and
   (q643826-family-extensional-p domain measurable)
   (q643826-family-valid-p domain measurable)
   (q643826-measurable-empty-exists-p domain measurable)
   (q643826-measurable-complements-p domain measurable)
   (q643826-measurable-sequence-unions-p domain measurable)))

(defun-sk q643826-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q643826-set-member-p left x)
      (q643826-set-member-p right x)))))

(defun-sk q643826-pairwise-disjoint-p (sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (q643826-disjoint-sets-p
      (q643826-set-sequence-value sequence m)
      (q643826-set-sequence-value sequence n)))))

(defun q643826-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q643826-ennreal-zero real)
    (q643826-ennreal-add
     real
     (q643826-measure-prefix-sum
      real measure sequence (1- count))
     (q643826-measure-value
      measure
      (q643826-set-sequence-value sequence (1- count))))))

(defun-sk q643826-countable-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q643826-ennreal-leq
      real
      (q643826-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q643826-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q643826-ennreal-p real total)
     (q643826-countable-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q643826-ennreal-p real bound)
       (q643826-countable-sum-upper-bound-p
        real measure sequence bound))
      (q643826-ennreal-leq real total bound)))))

(defun-sk q643826-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q643826-set-equiv-p domain left right)
     (equal
      (q643826-measure-value measure left)
      (q643826-measure-value measure right)))))

(defun-sk q643826-measure-values-p (real domain measure)
  (forall (set)
    (implies
     (q643826-valid-set-p domain set)
     (q643826-ennreal-p
      real (q643826-measure-value measure set)))))

(defun-sk q643826-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q643826-empty-set-p domain empty)
     (equal
      (q643826-measure-value measure empty)
      (q643826-ennreal-zero real)))))

(defun-sk q643826-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q643826-set-sequence-p domain sequence)
      (q643826-sequence-measurable-p measurable sequence)
      (q643826-pairwise-disjoint-p sequence)
      (q643826-sequence-union-set-p domain sequence union))
     (q643826-countable-sum-p
      real measure sequence
      (q643826-measure-value measure union)))))

(defun-sk q643826-measurable-superset-lower-bound-p
    (real measurable measure set lower)
  (forall (superset)
    (implies
     (and
      (q643826-measurable-set-p measurable superset)
      (q643826-set-subset-p set superset))
     (q643826-ennreal-leq
      real lower
      (q643826-measure-value measure superset)))))

(defun-sk q643826-outer-measure-value-p
    (real measurable measure set)
  (forall (lower)
    (and
     (q643826-measurable-superset-lower-bound-p
      real measurable measure set
      (q643826-measure-value measure set))
     (implies
      (and
       (q643826-ennreal-p real lower)
       (q643826-measurable-superset-lower-bound-p
        real measurable measure set lower))
      (q643826-ennreal-leq
       real lower
       (q643826-measure-value measure set))))))

(defun-sk q643826-outer-measure-values-p
    (real domain measurable measure)
  (forall (set)
    (implies
     (q643826-valid-set-p domain set)
     (q643826-outer-measure-value-p
      real measurable measure set))))

(defun q643826-measure-space-p
    (real domain measurable measure)
  (and
   (q643826-sigma-algebra-p domain measurable)
   (q643826-measure-extensional-p domain measure)
   (q643826-measure-values-p real domain measure)
   (q643826-measure-empty-zero-p real domain measure)
   (q643826-countably-additive-p
    real domain measurable measure)
   (q643826-outer-measure-values-p
    real domain measurable measure)))

(defun q643826-null-set-p (real domain measure set)
  (and
   (q643826-valid-set-p domain set)
   (equal
    (q643826-measure-value measure set)
    (q643826-ennreal-zero real))))

;; Typed functions and measurability through upper-ray preimages.

(defun-sk q643826-real-function-p (real domain function)
  (forall (x)
    (implies
     (q643826-domain-member-p domain x)
     (q643826-r-member-p
      real (q643826-function-value function x)))))

(defun-sk q643826-ennreal-function-p (real domain function)
  (forall (x)
    (implies
     (q643826-domain-member-p domain x)
     (q643826-ennreal-p
      real (q643826-function-value function x)))))

(defun-sk q643826-real-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q643826-set-member-p set x)
     (and
      (q643826-domain-member-p domain x)
      (q643826-r-less
       real threshold
       (q643826-function-value function x))))))

(defun-sk q643826-ennreal-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q643826-set-member-p set x)
     (and
      (q643826-domain-member-p domain x)
      (q643826-ennreal-less
       real threshold
       (q643826-function-value function x))))))

(defun-sk q643826-real-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q643826-real-upper-preimage-set-p
      real domain function threshold set)
     (q643826-measurable-set-p measurable set))))

(defun-sk q643826-ennreal-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q643826-ennreal-upper-preimage-set-p
      real domain function threshold set)
     (q643826-measurable-set-p measurable set))))

(defun-sk q643826-measurable-real-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q643826-real-function-p real domain function)
     (implies
      (q643826-r-member-p real threshold)
      (q643826-real-upper-preimage-exists-p
       real domain measurable function threshold)))))

(defun-sk q643826-measurable-ennreal-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q643826-ennreal-function-p real domain function)
     (implies
      (q643826-ennreal-p real threshold)
      (q643826-ennreal-upper-preimage-exists-p
       real domain measurable function threshold)))))

(defun-sk q643826-disagreement-set-p
    (domain left right set)
  (forall (x)
    (iff
     (q643826-set-member-p set x)
     (and
      (q643826-domain-member-p domain x)
      (not
       (equal
        (q643826-function-value left x)
        (q643826-function-value right x)))))))

(defun-sk q643826-ae-equal-p
    (real domain measure left right)
  (exists (set)
    (and
     (q643826-disagreement-set-p domain left right set)
     (q643826-null-set-p real domain measure set))))

(defun-sk q643826-ae-real-measurable-p
    (real domain measurable measure function)
  (exists (representative)
    (and
     (q643826-real-function-p real domain function)
     (q643826-measurable-real-function-p
      real domain measurable representative)
     (q643826-ae-equal-p
      real domain measure function representative))))

(defun-sk q643826-ae-ennreal-measurable-p
    (real domain measurable measure function)
  (exists (representative)
    (and
     (q643826-ennreal-function-p real domain function)
     (q643826-measurable-ennreal-function-p
      real domain measurable representative)
     (q643826-ae-equal-p
      real domain measure function representative))))

;; The lower Lebesgue integral as the supremum of measurable finite-range
;; simple functions below the integrand.

(defun-sk q643826-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q643826-domain-member-p domain x)
     (equal
      (q643826-function-value function x)
      value))))

(defun q643826-values-attained-p
    (domain function values)
  (if (consp values)
      (and
       (q643826-value-attained-p
        domain function (car values))
       (q643826-values-attained-p
        domain function (cdr values)))
    (equal values nil)))

(defun q643826-ennreal-value-list-p (real values)
  (if (consp values)
      (and
       (q643826-ennreal-p real (car values))
       (q643826-ennreal-value-list-p real (cdr values)))
    (equal values nil)))

(defun-sk q643826-range-in-values-p
    (domain function values)
  (forall (x)
    (implies
     (q643826-domain-member-p domain x)
     (member-equal
      (q643826-function-value function x)
      values))))

(defun-sk q643826-fiber-set-p
    (domain function value set)
  (forall (x)
    (iff
     (q643826-set-member-p set x)
     (and
      (q643826-domain-member-p domain x)
      (equal
       (q643826-function-value function x)
       value)))))

(defun q643826-fiber-list-p
    (domain function values fibers)
  (if (consp values)
      (and
       (consp fibers)
       (q643826-fiber-set-p
        domain function (car values) (car fibers))
       (q643826-fiber-list-p
        domain function (cdr values) (cdr fibers)))
    (equal fibers nil)))

(defun q643826-finite-simple-integral
    (real measure values fibers)
  (if (consp values)
      (q643826-ennreal-add
       real
       (q643826-ennreal-multiply
        real
        (car values)
        (q643826-measure-value measure (car fibers)))
       (q643826-finite-simple-integral
        real measure (cdr values) (cdr fibers)))
    (q643826-ennreal-zero real)))

(defun q643826-simple-function-data-p
    (real domain measurable function values fibers)
  (and
   (true-listp values)
   (true-listp fibers)
   (no-duplicatesp-equal values)
   (q643826-ennreal-value-list-p real values)
   (q643826-values-attained-p domain function values)
   (q643826-range-in-values-p domain function values)
   (q643826-fiber-list-p domain function values fibers)
   (q643826-measurable-ennreal-function-p
    real domain measurable function)))

(defun-sk q643826-simple-below-p
    (real domain simple function)
  (forall (x)
    (implies
     (q643826-domain-member-p domain x)
     (q643826-ennreal-leq
      real
      (q643826-function-value simple x)
      (q643826-function-value function x)))))

(defun-sk q643826-lintegral-upper-bound-p
    (real domain measurable measure function bound)
  (forall (simple values fibers)
    (implies
     (and
      (q643826-simple-function-data-p
       real domain measurable simple values fibers)
      (q643826-simple-below-p
       real domain simple function))
     (q643826-ennreal-leq
      real
      (q643826-finite-simple-integral
       real measure values fibers)
      bound))))

(defun-sk q643826-lintegral-value-p
    (real domain measurable measure function value)
  (forall (bound)
    (and
     (q643826-ennreal-function-p real domain function)
     (q643826-ennreal-p real value)
     (q643826-lintegral-upper-bound-p
      real domain measurable measure function value)
     (implies
      (and
       (q643826-ennreal-p real bound)
       (q643826-lintegral-upper-bound-p
        real domain measurable measure function bound))
      (q643826-ennreal-leq real value bound)))))

(defun-sk q643826-lintegral-operation-p
    (real domain measurable measure lintegral)
  (forall (function)
    (implies
     (q643826-ennreal-function-p real domain function)
     (q643826-lintegral-value-p
      real domain measurable measure function
      (q643826-lintegral-value
       lintegral domain measurable measure function)))))

;; The real Bochner integral, specialized to real-valued functions.

(defun-sk q643826-enorm-function-p
    (real domain function enorm-function)
  (forall (x)
    (and
     (q643826-ennreal-function-p real domain enorm-function)
     (implies
      (q643826-domain-member-p domain x)
      (equal
       (q643826-function-value enorm-function x)
       (q643826-ennreal-finite
        (q643826-r-abs
         real
         (q643826-function-value function x))))))))

(defun-sk q643826-integrable-enorm-exists-p
    (real domain measurable measure lintegral function)
  (exists (enorm-function)
    (and
     (q643826-enorm-function-p
      real domain function enorm-function)
     (q643826-ennreal-less
      real
      (q643826-lintegral-value
       lintegral domain measurable measure enorm-function)
      :q643826-top))))

(defun q643826-integrable-p
    (real domain measurable measure lintegral function)
  (and
   (q643826-ae-real-measurable-p
    real domain measurable measure function)
   (q643826-integrable-enorm-exists-p
    real domain measurable measure lintegral function)))

(defun-sk q643826-positive-part-function-p
    (real domain function positive)
  (forall (x)
    (and
     (q643826-ennreal-function-p real domain positive)
     (implies
      (q643826-domain-member-p domain x)
      (equal
       (q643826-function-value positive x)
       (q643826-ennreal-finite
        (if
            (q643826-r-less
             real
             (q643826-function-value function x)
             (q643826-r-zero real))
            (q643826-r-zero real)
          (q643826-function-value function x))))))))

(defun-sk q643826-negative-part-function-p
    (real domain function negative)
  (forall (x)
    (and
     (q643826-ennreal-function-p real domain negative)
     (implies
      (q643826-domain-member-p domain x)
      (let ((negated
             (q643826-r-negate
              real
              (q643826-function-value function x))))
        (equal
         (q643826-function-value negative x)
         (q643826-ennreal-finite
          (if
              (q643826-r-less
               real negated (q643826-r-zero real))
              (q643826-r-zero real)
            negated))))))))

(defun-sk q643826-real-integral-witness-exists-p
    (integral real domain measurable measure lintegral function value)
  (exists (positive negative)
    (and
     (q643826-positive-part-function-p
      real domain function positive)
     (q643826-negative-part-function-p
      real domain function negative)
     (equal
      value
      (q643826-r-add
       real
       (q643826-ennreal-to-real
        real
        (q643826-lintegral-value
         lintegral domain measurable measure positive))
       (q643826-r-negate
        real
        (q643826-ennreal-to-real
         real
         (q643826-lintegral-value
          lintegral domain measurable measure negative))))))))

(defun q643826-real-integral-value-p
    (integral real domain measurable measure lintegral function value)
  (and
   (q643826-r-member-p real value)
   (if
       (q643826-integrable-p
        real domain measurable measure lintegral function)
       (q643826-real-integral-witness-exists-p
        integral real domain measurable measure
        lintegral function value)
     (equal value (q643826-r-zero real)))))

(defun-sk q643826-real-integral-operation-p
    (integral real domain measurable measure lintegral)
  (forall (function)
    (implies
     (q643826-real-function-p real domain function)
     (q643826-real-integral-value-p
      integral real domain measurable measure lintegral function
      (q643826-integral-value
       integral real domain measurable measure
       lintegral function)))))

;; Generic functions, topologies, Borel sigma algebras, and filters.

(defun-sk q643826-function-p (domain codomain function)
  (forall (x)
    (implies
     (q643826-domain-member-p domain x)
     (q643826-domain-member-p
      codomain (q643826-function-value function x)))))

(defun-sk q643826-function2-p
    (left-domain right-domain codomain function)
  (forall (x y)
    (implies
     (and
      (q643826-domain-member-p left-domain x)
      (q643826-domain-member-p right-domain y))
     (q643826-domain-member-p
      codomain (q643826-function2-value function x y)))))

(defun-sk q643826-function-sequence-p
    (index domain codomain sequence)
  (forall (i)
    (implies
     (q643826-domain-member-p index i)
     (q643826-function-p
      domain codomain
      (q643826-function-sequence-value sequence i)))))

(defun-sk q643826-preimage-set-p
    (domain function codomain-set preimage)
  (forall (x)
    (iff
     (q643826-set-member-p preimage x)
     (and
      (q643826-domain-member-p domain x)
      (q643826-set-member-p
       codomain-set
       (q643826-function-value function x))))))

(defun-sk q643826-measurable-preimage-exists-p
    (domain domain-measurable function codomain-set)
  (exists (preimage)
    (and
     (q643826-preimage-set-p
      domain function codomain-set preimage)
     (q643826-measurable-set-p
      domain-measurable preimage))))

(defun-sk q643826-measurable-function-p
    (domain domain-measurable codomain codomain-measurable function)
  (forall (set)
    (and
     (q643826-function-p domain codomain function)
     (implies
      (q643826-measurable-set-p codomain-measurable set)
      (q643826-measurable-preimage-exists-p
       domain domain-measurable function set)))))

(defun-sk q643826-ae-measurable-p
    (real domain domain-measurable measure
     codomain codomain-measurable function)
  (exists (representative)
    (and
     (q643826-function-p domain codomain function)
     (q643826-measurable-function-p
      domain domain-measurable codomain codomain-measurable
      representative)
     (q643826-ae-equal-p
      real domain measure function representative))))

(defun-sk q643826-sequence-ae-measurable-p
    (real index domain domain-measurable measure
     codomain codomain-measurable sequence)
  (forall (i)
    (implies
     (q643826-domain-member-p index i)
     (q643826-ae-measurable-p
      real domain domain-measurable measure
      codomain codomain-measurable
      (q643826-function-sequence-value sequence i)))))

(defun-sk q643826-full-set-p (domain set)
  (forall (x)
    (iff
     (q643826-set-member-p set x)
     (q643826-domain-member-p domain x))))

(defun-sk q643826-intersection-set-p
    (domain left right intersection)
  (forall (x)
    (iff
     (q643826-set-member-p intersection x)
     (and
      (q643826-domain-member-p domain x)
      (q643826-set-member-p left x)
      (q643826-set-member-p right x)))))

(defun-sk q643826-family-union-member-p
    (family x)
  (exists (set)
    (and
     (q643826-set-family-member-p family set)
     (q643826-set-member-p set x))))

(defun-sk q643826-family-union-set-p
    (domain family union)
  (forall (x)
    (iff
     (q643826-set-member-p union x)
     (and
      (q643826-domain-member-p domain x)
      (q643826-family-union-member-p family x)))))

(defun-sk q643826-topology-extensional-p
    (domain topology)
  (forall (left right)
    (implies
     (q643826-set-equiv-p domain left right)
     (iff
      (q643826-open-set-p topology left)
      (q643826-open-set-p topology right)))))

(defun-sk q643826-topology-valid-p
    (domain topology)
  (forall (set)
    (implies
     (q643826-open-set-p topology set)
     (q643826-valid-set-p domain set))))

(defun-sk q643826-topology-full-exists-p
    (domain topology)
  (exists (full)
    (and
     (q643826-full-set-p domain full)
     (q643826-open-set-p topology full))))

(defun-sk q643826-topology-intersection-exists-p
    (domain topology left right)
  (exists (intersection)
    (and
     (q643826-intersection-set-p
      domain left right intersection)
     (q643826-open-set-p topology intersection))))

(defun-sk q643826-topology-intersections-p
    (domain topology)
  (forall (left right)
    (implies
     (and
      (q643826-open-set-p topology left)
      (q643826-open-set-p topology right))
     (q643826-topology-intersection-exists-p
      domain topology left right))))

(defun-sk q643826-open-family-p (topology family)
  (forall (set)
    (implies
     (q643826-set-family-member-p family set)
     (q643826-open-set-p topology set))))

(defun-sk q643826-topology-union-exists-p
    (domain topology family)
  (exists (union)
    (and
     (q643826-family-union-set-p domain family union)
     (q643826-open-set-p topology union))))

(defun-sk q643826-topology-unions-p
    (domain topology)
  (forall (family)
    (implies
     (q643826-open-family-p topology family)
     (q643826-topology-union-exists-p
      domain topology family))))

(defun q643826-topological-space-p (domain topology)
  (and
   (q643826-topology-extensional-p domain topology)
   (q643826-topology-valid-p domain topology)
   (q643826-topology-full-exists-p domain topology)
   (q643826-topology-intersections-p domain topology)
   (q643826-topology-unions-p domain topology)))

(defun-sk q643826-open-preimage-exists-p
    (domain domain-topology function codomain-open)
  (exists (preimage)
    (and
     (q643826-preimage-set-p
      domain function codomain-open preimage)
     (q643826-open-set-p domain-topology preimage))))

(defun-sk q643826-continuous-p
    (domain domain-topology codomain codomain-topology function)
  (forall (set)
    (and
     (q643826-function-p domain codomain function)
     (implies
      (q643826-open-set-p codomain-topology set)
      (q643826-open-preimage-exists-p
       domain domain-topology function set)))))

(defun-sk q643826-binary-neighborhood-maps-p
    (left-domain right-domain function
     left-open right-open target-open)
  (forall (u v)
    (implies
     (and
      (q643826-domain-member-p left-domain u)
      (q643826-domain-member-p right-domain v)
      (q643826-set-member-p left-open u)
      (q643826-set-member-p right-open v))
     (q643826-set-member-p
      target-open
      (q643826-function2-value function u v)))))

(defun-sk q643826-continuous-binary-local-p
    (left-domain left-topology right-domain right-topology
     codomain codomain-topology function x y target-open)
  (exists (left-open right-open)
    (and
     (q643826-open-set-p left-topology left-open)
     (q643826-open-set-p right-topology right-open)
     (q643826-set-member-p left-open x)
     (q643826-set-member-p right-open y)
     (q643826-binary-neighborhood-maps-p
      left-domain right-domain function
      left-open right-open target-open))))

(defun-sk q643826-continuous-binary-p
    (left-domain left-topology right-domain right-topology
     codomain codomain-topology function)
  (forall (x y target-open)
    (and
     (q643826-function2-p
      left-domain right-domain codomain function)
     (implies
      (and
       (q643826-domain-member-p left-domain x)
       (q643826-domain-member-p right-domain y)
       (q643826-open-set-p codomain-topology target-open)
       (q643826-set-member-p
        target-open
        (q643826-function2-value function x y)))
      (q643826-continuous-binary-local-p
       left-domain left-topology right-domain right-topology
       codomain codomain-topology function x y target-open)))))

(defun-sk q643826-topology-subset-sigma-p
    (topology measurable)
  (forall (set)
    (implies
     (q643826-open-set-p topology set)
     (q643826-measurable-set-p measurable set))))

(defun-sk q643826-borel-member-p
    (domain topology set)
  (forall (candidate)
    (implies
     (and
      (q643826-sigma-algebra-p domain candidate)
      (q643826-topology-subset-sigma-p topology candidate))
     (q643826-measurable-set-p candidate set))))

(defun-sk q643826-borel-space-p
    (domain topology measurable)
  (forall (set)
    (and
     (q643826-sigma-algebra-p domain measurable)
     (q643826-topological-space-p domain topology)
     (implies
      (q643826-valid-set-p domain set)
      (iff
       (q643826-measurable-set-p measurable set)
       (q643826-borel-member-p domain topology set))))))

(defun-sk q643826-basis-open-p
    (topology basis)
  (forall (n)
    (implies
     (natp n)
     (q643826-open-set-p
      topology (q643826-set-sequence-value basis n)))))

(defun-sk q643826-basis-refines-at-p
    (domain basis open x)
  (exists (n)
    (and
     (natp n)
     (q643826-set-member-p
      (q643826-set-sequence-value basis n) x)
     (q643826-set-subset-p
      (q643826-set-sequence-value basis n) open))))

(defun-sk q643826-countable-basis-p
    (domain topology basis)
  (forall (open x)
    (and
     (q643826-basis-open-p topology basis)
     (implies
      (and
       (q643826-open-set-p topology open)
       (q643826-domain-member-p domain x)
       (q643826-set-member-p open x))
      (q643826-basis-refines-at-p
       domain basis open x)))))

(defun-sk q643826-second-countable-topology-p
    (domain topology)
  (exists (basis)
    (q643826-countable-basis-p domain topology basis)))

(defun-sk q643826-filter-extensional-p
    (index filter)
  (forall (left right)
    (implies
     (q643826-set-equiv-p index left right)
     (iff
      (q643826-filter-set-p filter left)
      (q643826-filter-set-p filter right)))))

(defun-sk q643826-filter-valid-p
    (index filter)
  (forall (set)
    (implies
     (q643826-filter-set-p filter set)
     (q643826-valid-set-p index set))))

(defun-sk q643826-filter-full-exists-p
    (index filter)
  (exists (full)
    (and
     (q643826-full-set-p index full)
     (q643826-filter-set-p filter full))))

(defun-sk q643826-filter-upward-p
    (filter)
  (forall (left right)
    (implies
     (and
      (q643826-filter-set-p filter left)
      (q643826-set-subset-p left right))
     (q643826-filter-set-p filter right))))

(defun-sk q643826-filter-intersection-exists-p
    (index filter left right)
  (exists (intersection)
    (and
     (q643826-intersection-set-p
      index left right intersection)
     (q643826-filter-set-p filter intersection))))

(defun-sk q643826-filter-intersections-p
    (index filter)
  (forall (left right)
    (implies
     (and
      (q643826-filter-set-p filter left)
      (q643826-filter-set-p filter right))
     (q643826-filter-intersection-exists-p
      index filter left right))))

(defun q643826-filter-p (index filter)
  (and
   (q643826-filter-extensional-p index filter)
   (q643826-filter-valid-p index filter)
   (q643826-filter-full-exists-p index filter)
   (q643826-filter-upward-p filter)
   (q643826-filter-intersections-p index filter)))

(defun-sk q643826-filter-basis-member-p
    (filter basis)
  (forall (n)
    (implies
     (natp n)
     (q643826-filter-set-p
      filter (q643826-set-sequence-value basis n)))))

(defun-sk q643826-filter-basis-refines-p
    (filter basis set)
  (exists (n)
    (and
     (natp n)
     (q643826-set-subset-p
      (q643826-set-sequence-value basis n) set))))

(defun-sk q643826-countable-filter-basis-p
    (filter basis)
  (forall (set)
    (and
     (q643826-filter-basis-member-p filter basis)
     (implies
      (q643826-filter-set-p filter set)
      (q643826-filter-basis-refines-p
       filter basis set)))))

(defun-sk q643826-countably-generated-filter-p
    (filter)
  (exists (basis)
    (q643826-countable-filter-basis-p filter basis)))

(defun-sk q643826-neighborhood-preimage-exists-p
    (index filter function open)
  (exists (preimage)
    (and
     (q643826-preimage-set-p
      index function open preimage)
     (q643826-filter-set-p filter preimage))))

(defun-sk q643826-tendsto-p
    (index filter codomain topology function limit)
  (forall (open)
    (and
     (q643826-function-p index codomain function)
     (q643826-domain-member-p codomain limit)
     (implies
      (and
       (q643826-open-set-p topology open)
       (q643826-set-member-p open limit))
      (q643826-neighborhood-preimage-exists-p
       index filter function open)))))

;; Ordered-real topology and seminormed additive commutative groups.

(defun-sk q643826-real-ball-subset-p
    (real set x epsilon)
  (forall (y)
    (implies
     (and
      (q643826-r-member-p real y)
      (q643826-r-less
       real
       (q643826-r-abs
        real
        (q643826-r-add
         real y (q643826-r-negate real x)))
       epsilon))
     (q643826-set-member-p set y))))

(defun-sk q643826-real-open-at-p
    (real set x)
  (exists (epsilon)
    (and
     (q643826-r-member-p real epsilon)
     (q643826-r-less
      real (q643826-r-zero real) epsilon)
     (q643826-real-ball-subset-p
      real set x epsilon))))

(defun-sk q643826-real-open-set-p
    (real set)
  (forall (x)
    (and
     (q643826-valid-set-p real set)
     (implies
      (q643826-set-member-p set x)
      (q643826-real-open-at-p real set x)))))

(defun-sk q643826-real-topology-p
    (real topology)
  (forall (set)
    (and
     (q643826-topological-space-p real topology)
     (implies
      (q643826-valid-set-p real set)
      (iff
       (q643826-open-set-p topology set)
       (q643826-real-open-set-p real set))))))

(defun-sk q643826-additive-group-laws-p
    (carrier zero-operation add-operation negate-operation)
  (forall (x y z)
    (implies
     (and
      (q643826-domain-member-p carrier x)
      (q643826-domain-member-p carrier y)
      (q643826-domain-member-p carrier z))
     (let* ((zero (q643826-object-zero zero-operation))
            (xy (q643826-object-add add-operation x y))
            (yz (q643826-object-add add-operation y z))
            (neg-x (q643826-object-negate negate-operation x)))
       (and
        (q643826-domain-member-p carrier xy)
        (q643826-domain-member-p carrier neg-x)
        (equal
         (q643826-object-add add-operation xy z)
         (q643826-object-add add-operation x yz))
        (equal xy (q643826-object-add add-operation y x))
        (equal
         (q643826-object-add add-operation x zero)
         x)
        (equal
         (q643826-object-add add-operation x neg-x)
         zero))))))

(defun-sk q643826-seminorm-laws-p
    (real carrier zero-operation add-operation negate-operation
     norm-operation)
  (forall (x y)
    (implies
     (and
      (q643826-domain-member-p carrier x)
      (q643826-domain-member-p carrier y))
     (let* ((zero (q643826-object-zero zero-operation))
            (norm-x (q643826-norm-value norm-operation real x))
            (norm-y (q643826-norm-value norm-operation real y))
            (norm-sum
             (q643826-norm-value
              norm-operation real
              (q643826-object-add add-operation x y))))
       (and
        (q643826-r-member-p real norm-x)
        (not
         (q643826-r-less
          real norm-x (q643826-r-zero real)))
        (equal
         (q643826-norm-value norm-operation real zero)
         (q643826-r-zero real))
        (equal
         (q643826-norm-value
          norm-operation real
          (q643826-object-negate negate-operation x))
         norm-x)
        (q643826-r-leq
         real norm-sum
         (q643826-r-add real norm-x norm-y)))))))

(defun q643826-object-distance
    (real add-operation negate-operation norm-operation left right)
  (q643826-norm-value
   norm-operation real
   (q643826-object-add
    add-operation left
    (q643826-object-negate negate-operation right))))

(defun-sk q643826-norm-ball-subset-p
    (real carrier add-operation negate-operation norm-operation
     set x epsilon)
  (forall (y)
    (implies
     (and
      (q643826-domain-member-p carrier y)
      (q643826-r-less
       real
       (q643826-object-distance
        real add-operation negate-operation norm-operation
        y x)
       epsilon))
     (q643826-set-member-p set y))))

(defun-sk q643826-norm-open-at-p
    (real carrier add-operation negate-operation norm-operation
     set x)
  (exists (epsilon)
    (and
     (q643826-r-member-p real epsilon)
     (q643826-r-less
      real (q643826-r-zero real) epsilon)
     (q643826-norm-ball-subset-p
      real carrier add-operation negate-operation norm-operation
      set x epsilon))))

(defun-sk q643826-norm-open-set-p
    (real carrier add-operation negate-operation norm-operation set)
  (forall (x)
    (and
     (q643826-valid-set-p carrier set)
     (implies
      (q643826-set-member-p set x)
      (q643826-norm-open-at-p
       real carrier add-operation negate-operation norm-operation
       set x)))))

(defun-sk q643826-norm-topology-p
    (real carrier add-operation negate-operation norm-operation
     topology)
  (forall (set)
    (and
     (q643826-topological-space-p carrier topology)
     (implies
      (q643826-valid-set-p carrier set)
      (iff
       (q643826-open-set-p topology set)
       (q643826-norm-open-set-p
        real carrier add-operation negate-operation norm-operation
        set))))))

(defun q643826-seminormed-add-comm-group-p
    (real carrier zero-operation add-operation negate-operation
     norm-operation topology)
  (and
   (q643826-domain-member-p
    carrier (q643826-object-zero zero-operation))
   (q643826-additive-group-laws-p
    carrier zero-operation add-operation negate-operation)
   (q643826-seminorm-laws-p
    real carrier zero-operation add-operation negate-operation
    norm-operation)
   (q643826-norm-topology-p
    real carrier add-operation negate-operation norm-operation
    topology)))

;; Probability measures and bounded-continuous-test-function weak convergence.

(defun-sk q643826-probability-full-p
    (real domain measure)
  (exists (full)
    (and
     (q643826-full-set-p domain full)
     (equal
      (q643826-measure-value measure full)
      (q643826-ennreal-finite
       (q643826-r-one real))))))

(defun q643826-probability-space-p
    (real domain measurable measure)
  (and
   (q643826-measure-space-p
    real domain measurable measure)
   (q643826-probability-full-p
    real domain measure)))

(defun-sk q643826-real-function-bounded-by-p
    (real domain function bound)
  (forall (x)
    (implies
     (q643826-domain-member-p domain x)
     (q643826-r-leq
      real
      (q643826-r-abs
       real (q643826-function-value function x))
      bound))))

(defun-sk q643826-bounded-real-function-p
    (real domain function)
  (exists (bound)
    (and
     (q643826-r-member-p real bound)
     (q643826-r-leq
      real (q643826-r-zero real) bound)
     (q643826-real-function-bounded-by-p
      real domain function bound))))

(defun q643826-bounded-continuous-real-function-p
    (real real-topology domain topology function)
  (and
   (q643826-real-function-p real domain function)
   (q643826-continuous-p
    domain topology real real-topology function)
   (q643826-bounded-real-function-p
    real domain function)))

(defun-sk q643826-composition-function-p
    (domain middle inner outer composition)
  (forall (x)
    (and
     (q643826-function-p domain middle inner)
     (implies
      (q643826-domain-member-p domain x)
      (equal
       (q643826-function-value composition x)
       (q643826-function-value
        outer (q643826-function-value inner x)))))))

(defun-sk q643826-composed-function-sequence-p
    (index domain middle inner-sequence outer
     composition-sequence)
  (forall (i)
    (implies
     (q643826-domain-member-p index i)
     (q643826-composition-function-p
      domain middle
      (q643826-function-sequence-value inner-sequence i)
      outer
      (q643826-function-sequence-value
       composition-sequence i)))))

(defun-sk q643826-integral-value-sequence-p
    (real index domain measurable measure lintegral integral
     integrand-sequence value-sequence)
  (forall (i)
    (implies
     (q643826-domain-member-p index i)
     (equal
      (q643826-function-value value-sequence i)
      (q643826-integral-value
       integral real domain measurable measure lintegral
       (q643826-function-sequence-value
        integrand-sequence i))))))

(defun-sk q643826-test-integrals-tendsto-p
    (real real-topology index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral source-sequence
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral limit-function
     codomain test)
  (exists
      (source-integrands source-values limit-integrand)
    (and
     (q643826-composed-function-sequence-p
      index source-domain codomain source-sequence test
      source-integrands)
     (q643826-composition-function-p
      limit-domain codomain limit-function test
      limit-integrand)
     (q643826-integral-value-sequence-p
      real index source-domain source-measurable source-measure
      source-lintegral source-integral
      source-integrands source-values)
     (q643826-tendsto-p
      index filter real real-topology source-values
      (q643826-integral-value
       limit-integral real limit-domain limit-measurable
       limit-measure limit-lintegral limit-integrand)))))

(defun-sk q643826-weak-convergence-p
    (real real-topology index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral source-sequence
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral limit-function
     codomain codomain-topology)
  (forall (test)
    (implies
     (q643826-bounded-continuous-real-function-p
      real real-topology codomain codomain-topology test)
     (q643826-test-integrals-tendsto-p
      real real-topology index filter
      source-domain source-measurable source-measure
      source-lintegral source-integral source-sequence
      limit-domain limit-measurable limit-measure
      limit-lintegral limit-integral limit-function
      codomain test))))

(defun q643826-tendsto-in-distribution-p
    (real real-topology index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral source-sequence
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral limit-function
     codomain codomain-topology codomain-measurable)
  (and
   (q643826-sequence-ae-measurable-p
    real index source-domain source-measurable source-measure
    codomain codomain-measurable source-sequence)
   (q643826-ae-measurable-p
    real limit-domain limit-measurable limit-measure
    codomain codomain-measurable limit-function)
   (q643826-weak-convergence-p
    real real-topology index filter
    source-domain source-measurable source-measure
    source-lintegral source-integral source-sequence
    limit-domain limit-measurable limit-measure
    limit-lintegral limit-integral limit-function
    codomain codomain-topology)))

;; Convergence in measure to a constant, using the equivalent real-valued
;; probability-of-deviation formulation.

(defun-sk q643826-deviation-set-p
    (real source-domain codomain add-operation negate-operation
     norm-operation function constant epsilon set)
  (forall (omega)
    (iff
     (q643826-set-member-p set omega)
     (and
      (q643826-domain-member-p source-domain omega)
      (q643826-r-leq
       real epsilon
       (q643826-norm-value
        norm-operation real
        (q643826-object-add
         add-operation
         (q643826-function-value function omega)
         (q643826-object-negate
          negate-operation constant))))))))

(defun-sk q643826-deviation-set-sequence-p
    (real index source-domain codomain
     add-operation negate-operation norm-operation
     function-sequence constant epsilon set-sequence)
  (forall (i)
    (implies
     (q643826-domain-member-p index i)
     (q643826-deviation-set-p
      real source-domain codomain
      add-operation negate-operation norm-operation
      (q643826-function-sequence-value function-sequence i)
      constant epsilon
      (q643826-set-sequence-value set-sequence i)))))

(defun-sk q643826-deviation-measure-values-p
    (real index measure set-sequence values)
  (forall (i)
    (implies
     (q643826-domain-member-p index i)
     (equal
      (q643826-function-value values i)
      (q643826-ennreal-to-real
       real
       (q643826-measure-value
        measure
        (q643826-set-sequence-value set-sequence i)))))))

(defun-sk q643826-tendsto-in-measure-at-p
    (real real-topology index filter source-domain measure
     codomain add-operation negate-operation norm-operation
     function-sequence constant epsilon)
  (exists (deviation-sets values)
    (and
     (q643826-deviation-set-sequence-p
      real index source-domain codomain
      add-operation negate-operation norm-operation
      function-sequence constant epsilon deviation-sets)
     (q643826-deviation-measure-values-p
      real index measure deviation-sets values)
     (q643826-tendsto-p
      index filter real real-topology values
      (q643826-r-zero real)))))

(defun-sk q643826-tendsto-in-measure-const-p
    (real real-topology index filter source-domain measure
     codomain add-operation negate-operation norm-operation
     function-sequence constant)
  (forall (epsilon)
    (implies
     (and
      (q643826-r-member-p real epsilon)
      (q643826-r-less
       real (q643826-r-zero real) epsilon))
     (q643826-tendsto-in-measure-at-p
      real real-topology index filter source-domain measure
      codomain add-operation negate-operation norm-operation
      function-sequence constant epsilon))))

;; The pointwise compositions in the conclusion are internal existential
;; witnesses, exactly as in the source lambda expressions.

(defun-sk q643826-slutsky-source-composition-p
    (index source-domain left-codomain right-codomain
     target-codomain left-sequence right-sequence function
     composition-sequence)
  (forall (i omega)
    (and
     (q643826-function-sequence-p
      index source-domain target-codomain composition-sequence)
     (implies
      (and
       (q643826-domain-member-p index i)
       (q643826-domain-member-p source-domain omega))
      (equal
       (q643826-function-value
        (q643826-function-sequence-value composition-sequence i)
        omega)
       (q643826-function2-value
        function
        (q643826-function-value
         (q643826-function-sequence-value left-sequence i)
         omega)
        (q643826-function-value
         (q643826-function-sequence-value right-sequence i)
         omega)))))))

(defun-sk q643826-slutsky-limit-composition-p
    (limit-domain left-codomain right-codomain target-codomain
     limit-function constant function composition)
  (forall (omega)
    (and
     (q643826-function-p
      limit-domain target-codomain composition)
     (implies
      (q643826-domain-member-p limit-domain omega)
      (equal
       (q643826-function-value composition omega)
       (q643826-function2-value
        function
        (q643826-function-value limit-function omega)
        constant))))))

(defun-sk q643826-slutsky-conclusion-p
    (real real-topology index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral
     left-codomain right-codomain target-codomain
     target-topology target-measurable
     left-sequence right-sequence limit-function constant function)
  (exists (composition-sequence composition-limit)
    (and
     (q643826-slutsky-source-composition-p
      index source-domain left-codomain right-codomain
      target-codomain left-sequence right-sequence function
      composition-sequence)
     (q643826-slutsky-limit-composition-p
      limit-domain left-codomain right-codomain target-codomain
      limit-function constant function composition-limit)
     (q643826-tendsto-in-distribution-p
      real real-topology index filter
      source-domain source-measurable source-measure
      source-lintegral source-integral composition-sequence
      limit-domain limit-measurable limit-measure
      limit-lintegral limit-integral composition-limit
      target-codomain target-topology target-measurable))))

(defun q643826-canonical-context-p
    (real real-topology
     index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral
     left-codomain left-zero left-add left-negate left-norm
     left-topology left-measurable
     right-codomain right-zero right-add right-negate right-norm
     right-topology right-measurable
     target-codomain target-topology target-measurable
     left-sequence right-sequence limit-function constant function)
  (and
   (q643826-real-field-p real)
   (q643826-real-topology-p real real-topology)
   (q643826-filter-p index filter)
   (q643826-countably-generated-filter-p filter)
   (q643826-probability-space-p
    real source-domain source-measurable source-measure)
   (q643826-lintegral-operation-p
    real source-domain source-measurable source-measure
    source-lintegral)
   (q643826-real-integral-operation-p
    source-integral real source-domain source-measurable
    source-measure source-lintegral)
   (q643826-probability-space-p
    real limit-domain limit-measurable limit-measure)
   (q643826-lintegral-operation-p
    real limit-domain limit-measurable limit-measure
    limit-lintegral)
   (q643826-real-integral-operation-p
    limit-integral real limit-domain limit-measurable
    limit-measure limit-lintegral)
   (q643826-seminormed-add-comm-group-p
    real left-codomain left-zero left-add left-negate left-norm
    left-topology)
   (q643826-second-countable-topology-p
    left-codomain left-topology)
   (q643826-borel-space-p
    left-codomain left-topology left-measurable)
   (q643826-seminormed-add-comm-group-p
    real right-codomain right-zero right-add right-negate right-norm
    right-topology)
   (q643826-second-countable-topology-p
    right-codomain right-topology)
   (q643826-borel-space-p
    right-codomain right-topology right-measurable)
   (q643826-topological-space-p
    target-codomain target-topology)
   (q643826-borel-space-p
    target-codomain target-topology target-measurable)
   (q643826-function-sequence-p
    index source-domain left-codomain left-sequence)
   (q643826-function-sequence-p
    index source-domain right-codomain right-sequence)
   (q643826-function-p
    limit-domain left-codomain limit-function)
   (q643826-domain-member-p right-codomain constant)
   (q643826-continuous-binary-p
    left-codomain left-topology
    right-codomain right-topology
    target-codomain target-topology function)))

(defun thousand-theorems-q643826-canonical-statement
    (real real-topology
     index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral
     left-codomain left-zero left-add left-negate left-norm
     left-topology left-measurable
     right-codomain right-zero right-add right-negate right-norm
     right-topology right-measurable
     target-codomain target-topology target-measurable
     left-sequence right-sequence limit-function constant function)
  (implies
   (and
    (q643826-canonical-context-p
     real real-topology
     index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral
     left-codomain left-zero left-add left-negate left-norm
     left-topology left-measurable
     right-codomain right-zero right-add right-negate right-norm
     right-topology right-measurable
     target-codomain target-topology target-measurable
     left-sequence right-sequence limit-function constant function)
    (q643826-tendsto-in-distribution-p
     real real-topology index filter
     source-domain source-measurable source-measure
     source-lintegral source-integral left-sequence
     limit-domain limit-measurable limit-measure
     limit-lintegral limit-integral limit-function
     left-codomain left-topology left-measurable)
    (q643826-tendsto-in-measure-const-p
     real real-topology index filter source-domain source-measure
     right-codomain right-add right-negate right-norm
     right-sequence constant)
    (q643826-sequence-ae-measurable-p
     real index source-domain source-measurable source-measure
     right-codomain right-measurable right-sequence))
   (q643826-slutsky-conclusion-p
    real real-topology index filter
    source-domain source-measurable source-measure
    source-lintegral source-integral
    limit-domain limit-measurable limit-measure
    limit-lintegral limit-integral
    left-codomain right-codomain target-codomain
    target-topology target-measurable
    left-sequence right-sequence limit-function constant function)))

(value-triple :itpeval-statement-checked)
:q
