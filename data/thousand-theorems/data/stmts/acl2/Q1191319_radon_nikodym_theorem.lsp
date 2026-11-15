;; Statement-only formalization of thousand-theorems corpus artifact Q1191319,
;; "Radon-Nikodym theorem": for arbitrary measures admitting a Lebesgue
;; decomposition, absolute continuity is equivalent to reconstruction of the
;; first measure by weighting the second with its Radon-Nikodym derivative.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The conservative interfaces below range over unrestricted ACL2 objects.
;; Their laws explicitly present a complete ordered real field, extended
;; nonnegative reals, arbitrary sets and functions, a sigma algebra,
;; countably additive measures, and the lower Lebesgue integral.  The
;; Radon-Nikodym derivative remains the internally chosen function from the
;; source's HaveLebesgueDecomposition witness.

;; Real scalars and arbitrary mathematical objects.

(defstub q1191319-r-member-p (real value) t)
(defstub q1191319-r-zero (real) t)
(defstub q1191319-r-one (real) t)
(defstub q1191319-r-add (real left right) t)
(defstub q1191319-r-multiply (real left right) t)
(defstub q1191319-r-negate (real value) t)
(defstub q1191319-r-inverse (real value) t)
(defstub q1191319-r-less (real left right) t)
(defstub q1191319-r-set-member-p (real set value) t)

(defstub q1191319-domain-member-p (domain value) t)
(defstub q1191319-set-member-p (set value) t)
(defstub q1191319-function-value (function argument) t)
(defstub q1191319-set-sequence-value (sequence index) t)
(defstub q1191319-measurable-set-p (measurable set) t)
(defstub q1191319-measure-value (measure set) t)
(defstub q1191319-lintegral-value
  (lintegral domain measurable measure function) t)

(defun q1191319-r-leq (real left right)
  (not (q1191319-r-less real right left)))

(defun-sk q1191319-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1191319-r-member-p real x)
      (q1191319-r-member-p real y)
      (q1191319-r-member-p real z))
     (let* ((zero (q1191319-r-zero real))
            (one (q1191319-r-one real))
            (xy-add (q1191319-r-add real x y))
            (yz-add (q1191319-r-add real y z))
            (xy-mul (q1191319-r-multiply real x y))
            (yz-mul (q1191319-r-multiply real y z))
            (neg-x (q1191319-r-negate real x))
            (inv-x (q1191319-r-inverse real x)))
       (and
        (q1191319-r-member-p real xy-add)
        (q1191319-r-member-p real xy-mul)
        (q1191319-r-member-p real neg-x)
        (q1191319-r-member-p real inv-x)
        (equal
         (q1191319-r-add real xy-add z)
         (q1191319-r-add real x yz-add))
        (equal xy-add (q1191319-r-add real y x))
        (equal (q1191319-r-add real x zero) x)
        (equal (q1191319-r-add real x neg-x) zero)
        (equal
         (q1191319-r-multiply real xy-mul z)
         (q1191319-r-multiply real x yz-mul))
        (equal xy-mul (q1191319-r-multiply real y x))
        (equal (q1191319-r-multiply real x one) x)
        (equal (q1191319-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1191319-r-multiply real x inv-x)
          one))
        (equal
         (q1191319-r-multiply
          real x (q1191319-r-add real y z))
         (q1191319-r-add
          real
          (q1191319-r-multiply real x y)
          (q1191319-r-multiply real x z))))))))

(defun-sk q1191319-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1191319-r-member-p real x)
      (q1191319-r-member-p real y)
      (q1191319-r-member-p real z))
     (let ((zero (q1191319-r-zero real)))
       (and
        (not (q1191319-r-less real x x))
        (or
         (equal x y)
         (q1191319-r-less real x y)
         (q1191319-r-less real y x))
        (implies
         (and
          (q1191319-r-less real x y)
          (q1191319-r-less real y z))
         (q1191319-r-less real x z))
        (implies
         (q1191319-r-less real x y)
         (q1191319-r-less
          real
          (q1191319-r-add real x z)
          (q1191319-r-add real y z)))
        (implies
         (and
          (q1191319-r-less real zero x)
          (q1191319-r-less real zero y))
         (q1191319-r-less
          real zero
          (q1191319-r-multiply real x y))))))))

(defun-sk q1191319-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q1191319-r-member-p real x)
     (q1191319-r-set-member-p real set x))))

(defun-sk q1191319-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q1191319-r-member-p real x)
      (q1191319-r-set-member-p real set x))
     (q1191319-r-leq real x bound))))

(defun-sk q1191319-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q1191319-r-member-p real bound)
     (q1191319-r-upper-bound-p real set bound))))

(defun-sk q1191319-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q1191319-r-member-p real supremum)
     (q1191319-r-upper-bound-p real set supremum)
     (implies
      (and
       (q1191319-r-member-p real bound)
       (q1191319-r-upper-bound-p real set bound))
      (q1191319-r-leq real supremum bound)))))

(defun-sk q1191319-r-has-supremum-p (real set)
  (exists (supremum)
    (q1191319-r-supremum-p real set supremum)))

(defun-sk q1191319-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q1191319-r-set-nonempty-p real set)
      (q1191319-r-bounded-above-p real set))
     (q1191319-r-has-supremum-p real set))))

(defun q1191319-real-field-p (real)
  (let ((zero (q1191319-r-zero real))
        (one (q1191319-r-one real)))
    (and
     (q1191319-r-member-p real zero)
     (q1191319-r-member-p real one)
     (not (equal zero one))
     (q1191319-r-field-laws-p real)
     (q1191319-r-order-laws-p real)
     (q1191319-r-less real zero one)
     (q1191319-r-dedekind-complete-p real))))

;; Extended nonnegative reals.

(defun q1191319-ennreal-p (real value)
  (or
   (equal value :q1191319-top)
   (and
    (consp value)
    (equal (car value) :q1191319-finite)
    (q1191319-r-member-p real (cdr value))
    (q1191319-r-leq
     real (q1191319-r-zero real) (cdr value)))))

(defun q1191319-ennreal-finite (value)
  (cons :q1191319-finite value))

(defun q1191319-ennreal-zero (real)
  (q1191319-ennreal-finite (q1191319-r-zero real)))

(defun q1191319-ennreal-less (real left right)
  (cond
   ((equal left :q1191319-top) nil)
   ((equal right :q1191319-top) t)
   (t (q1191319-r-less real (cdr left) (cdr right)))))

(defun q1191319-ennreal-leq (real left right)
  (not (q1191319-ennreal-less real right left)))

(defun q1191319-ennreal-add (real left right)
  (if (or (equal left :q1191319-top)
          (equal right :q1191319-top))
      :q1191319-top
    (q1191319-ennreal-finite
     (q1191319-r-add real (cdr left) (cdr right)))))

(defun q1191319-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q1191319-ennreal-zero real))
        (equal right (q1191319-ennreal-zero real)))
    (q1191319-ennreal-zero real))
   ((or (equal left :q1191319-top)
        (equal right :q1191319-top))
    :q1191319-top)
   (t
    (q1191319-ennreal-finite
     (q1191319-r-multiply real (cdr left) (cdr right))))))

;; Sets, sigma algebras, and countably additive measures.

(defun-sk q1191319-valid-set-p (domain set)
  (forall (x)
    (implies
     (q1191319-set-member-p set x)
     (q1191319-domain-member-p domain x))))

(defun-sk q1191319-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q1191319-domain-member-p domain x)
     (iff
      (q1191319-set-member-p left x)
      (q1191319-set-member-p right x)))))

(defun-sk q1191319-empty-set-p (domain set)
  (forall (x)
    (iff
     (q1191319-set-member-p set x)
     (and (q1191319-domain-member-p domain x) nil))))

(defun-sk q1191319-complement-set-p (domain set complement)
  (forall (x)
    (iff
     (q1191319-set-member-p complement x)
     (and
      (q1191319-domain-member-p domain x)
      (not (q1191319-set-member-p set x))))))

(defun-sk q1191319-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q1191319-valid-set-p
      domain
      (q1191319-set-sequence-value sequence n)))))

(defun-sk q1191319-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q1191319-set-member-p
      (q1191319-set-sequence-value sequence n)
      x))))

(defun-sk q1191319-sequence-union-set-p
    (domain sequence union)
  (forall (x)
    (iff
     (q1191319-set-member-p union x)
     (and
      (q1191319-domain-member-p domain x)
      (q1191319-sequence-union-member-p sequence x)))))

(defun-sk q1191319-family-extensional-p (domain measurable)
  (forall (left right)
    (implies
     (q1191319-set-equiv-p domain left right)
     (iff
      (q1191319-measurable-set-p measurable left)
      (q1191319-measurable-set-p measurable right)))))

(defun-sk q1191319-family-valid-p (domain measurable)
  (forall (set)
    (implies
     (q1191319-measurable-set-p measurable set)
     (q1191319-valid-set-p domain set))))

(defun-sk q1191319-measurable-empty-exists-p (domain measurable)
  (exists (empty)
    (and
     (q1191319-empty-set-p domain empty)
     (q1191319-measurable-set-p measurable empty))))

(defun-sk q1191319-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q1191319-complement-set-p domain set complement)
     (q1191319-measurable-set-p measurable complement))))

(defun-sk q1191319-measurable-complements-p
    (domain measurable)
  (forall (set)
    (implies
     (q1191319-measurable-set-p measurable set)
     (q1191319-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q1191319-sequence-measurable-p (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q1191319-measurable-set-p
      measurable
      (q1191319-set-sequence-value sequence n)))))

(defun-sk q1191319-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q1191319-sequence-union-set-p domain sequence union)
     (q1191319-measurable-set-p measurable union))))

(defun-sk q1191319-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q1191319-set-sequence-p domain sequence)
      (q1191319-sequence-measurable-p measurable sequence))
     (q1191319-measurable-union-exists-p
      domain measurable sequence))))

(defun q1191319-sigma-algebra-p (domain measurable)
  (and
   (q1191319-family-extensional-p domain measurable)
   (q1191319-family-valid-p domain measurable)
   (q1191319-measurable-empty-exists-p domain measurable)
   (q1191319-measurable-complements-p domain measurable)
   (q1191319-measurable-sequence-unions-p domain measurable)))

(defun-sk q1191319-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q1191319-set-member-p left x)
      (q1191319-set-member-p right x)))))

(defun-sk q1191319-pairwise-disjoint-p (sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (q1191319-disjoint-sets-p
      (q1191319-set-sequence-value sequence m)
      (q1191319-set-sequence-value sequence n)))))

(defun q1191319-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1191319-ennreal-zero real)
    (q1191319-ennreal-add
     real
     (q1191319-measure-prefix-sum
      real measure sequence (1- count))
     (q1191319-measure-value
      measure
      (q1191319-set-sequence-value sequence (1- count))))))

(defun-sk q1191319-countable-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q1191319-ennreal-leq
      real
      (q1191319-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q1191319-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q1191319-ennreal-p real total)
     (q1191319-countable-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q1191319-ennreal-p real bound)
       (q1191319-countable-sum-upper-bound-p
        real measure sequence bound))
      (q1191319-ennreal-leq real total bound)))))

(defun-sk q1191319-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q1191319-set-equiv-p domain left right)
     (equal
      (q1191319-measure-value measure left)
      (q1191319-measure-value measure right)))))

(defun-sk q1191319-measure-values-p
    (real domain measurable measure)
  (forall (set)
    (implies
     (and
      (q1191319-valid-set-p domain set)
      (q1191319-measurable-set-p measurable set))
     (q1191319-ennreal-p
      real (q1191319-measure-value measure set)))))

(defun-sk q1191319-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q1191319-empty-set-p domain empty)
     (equal
      (q1191319-measure-value measure empty)
      (q1191319-ennreal-zero real)))))

(defun-sk q1191319-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q1191319-set-sequence-p domain sequence)
      (q1191319-sequence-measurable-p measurable sequence)
      (q1191319-pairwise-disjoint-p sequence)
      (q1191319-sequence-union-set-p domain sequence union))
     (q1191319-countable-sum-p
      real measure sequence
      (q1191319-measure-value measure union)))))

(defun q1191319-measure-space-p
    (real domain measurable measure)
  (and
   (q1191319-sigma-algebra-p domain measurable)
   (q1191319-measure-extensional-p domain measure)
   (q1191319-measure-values-p real domain measurable measure)
   (q1191319-measure-empty-zero-p real domain measure)
   (q1191319-countably-additive-p
    real domain measurable measure)))

;; Measurable extended-nonnegative-real functions.

(defun-sk q1191319-ennreal-function-p (real domain function)
  (forall (x)
    (implies
     (q1191319-domain-member-p domain x)
     (q1191319-ennreal-p
      real (q1191319-function-value function x)))))

(defun-sk q1191319-ennreal-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q1191319-set-member-p set x)
     (and
      (q1191319-domain-member-p domain x)
      (q1191319-ennreal-less
       real threshold
       (q1191319-function-value function x))))))

(defun-sk q1191319-ennreal-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q1191319-ennreal-upper-preimage-set-p
      real domain function threshold set)
     (q1191319-measurable-set-p measurable set))))

(defun-sk q1191319-measurable-ennreal-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q1191319-ennreal-function-p real domain function)
     (implies
      (q1191319-ennreal-p real threshold)
      (q1191319-ennreal-upper-preimage-exists-p
       real domain measurable function threshold)))))

;; The lower Lebesgue integral is the supremum of integrals of measurable
;; finite-range simple functions below the integrand.

(defun-sk q1191319-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q1191319-domain-member-p domain x)
     (equal
      (q1191319-function-value function x)
      value))))

(defun q1191319-values-attained-p
    (domain function values)
  (if (consp values)
      (and
       (q1191319-value-attained-p
        domain function (car values))
       (q1191319-values-attained-p
        domain function (cdr values)))
    (equal values nil)))

(defun q1191319-ennreal-value-list-p (real values)
  (if (consp values)
      (and
       (q1191319-ennreal-p real (car values))
       (q1191319-ennreal-value-list-p real (cdr values)))
    (equal values nil)))

(defun-sk q1191319-range-in-values-p
    (domain function values)
  (forall (x)
    (implies
     (q1191319-domain-member-p domain x)
     (member-equal
      (q1191319-function-value function x)
      values))))

(defun-sk q1191319-fiber-set-p
    (domain function value set)
  (forall (x)
    (iff
     (q1191319-set-member-p set x)
     (and
      (q1191319-domain-member-p domain x)
      (equal
       (q1191319-function-value function x)
       value)))))

(defun q1191319-fiber-list-p
    (domain function values fibers)
  (if (consp values)
      (and
       (consp fibers)
       (q1191319-fiber-set-p
        domain function (car values) (car fibers))
       (q1191319-fiber-list-p
        domain function (cdr values) (cdr fibers)))
    (equal fibers nil)))

(defun q1191319-finite-simple-integral
    (real measure values fibers)
  (if (consp values)
      (q1191319-ennreal-add
       real
       (q1191319-ennreal-multiply
        real
        (car values)
        (q1191319-measure-value measure (car fibers)))
       (q1191319-finite-simple-integral
        real measure (cdr values) (cdr fibers)))
    (q1191319-ennreal-zero real)))

(defun q1191319-simple-function-data-p
    (real domain measurable function values fibers)
  (and
   (true-listp values)
   (true-listp fibers)
   (no-duplicatesp-equal values)
   (q1191319-ennreal-value-list-p real values)
   (q1191319-values-attained-p domain function values)
   (q1191319-range-in-values-p domain function values)
   (q1191319-fiber-list-p domain function values fibers)
   (q1191319-measurable-ennreal-function-p
    real domain measurable function)))

(defun-sk q1191319-simple-below-p
    (real domain simple function)
  (forall (x)
    (implies
     (q1191319-domain-member-p domain x)
     (q1191319-ennreal-leq
      real
      (q1191319-function-value simple x)
      (q1191319-function-value function x)))))

(defun-sk q1191319-lintegral-upper-bound-p
    (real domain measurable measure function bound)
  (forall (simple values fibers)
    (implies
     (and
      (q1191319-simple-function-data-p
       real domain measurable simple values fibers)
      (q1191319-simple-below-p
       real domain simple function))
     (q1191319-ennreal-leq
      real
      (q1191319-finite-simple-integral
       real measure values fibers)
      bound))))

(defun-sk q1191319-lintegral-value-p
    (real domain measurable measure function value)
  (forall (bound)
    (and
     (q1191319-ennreal-function-p real domain function)
     (q1191319-ennreal-p real value)
     (q1191319-lintegral-upper-bound-p
      real domain measurable measure function value)
     (implies
      (and
       (q1191319-ennreal-p real bound)
       (q1191319-lintegral-upper-bound-p
        real domain measurable measure function bound))
      (q1191319-ennreal-leq real value bound)))))

(defun-sk q1191319-lintegral-operation-p
    (real domain measurable lintegral)
  (forall (measure function)
    (implies
     (and
      (q1191319-measure-space-p
       real domain measurable measure)
      (q1191319-ennreal-function-p real domain function))
     (q1191319-lintegral-value-p
      real domain measurable measure function
      (q1191319-lintegral-value
       lintegral domain measurable measure function)))))

;; Measure equality, addition, absolute continuity, and mutual singularity.

(defun-sk q1191319-measure-equal-p
    (domain measurable left right)
  (forall (set)
    (implies
     (q1191319-measurable-set-p measurable set)
     (equal
      (q1191319-measure-value left set)
      (q1191319-measure-value right set)))))

(defun-sk q1191319-measure-addition-p
    (real measurable left right total)
  (forall (set)
    (implies
     (q1191319-measurable-set-p measurable set)
     (equal
      (q1191319-measure-value total set)
      (q1191319-ennreal-add
       real
       (q1191319-measure-value left set)
       (q1191319-measure-value right set))))))

(defun-sk q1191319-absolutely-continuous-p
    (real measurable mu nu)
  (forall (set)
    (implies
     (and
      (q1191319-measurable-set-p measurable set)
      (equal
       (q1191319-measure-value nu set)
       (q1191319-ennreal-zero real)))
     (equal
      (q1191319-measure-value mu set)
      (q1191319-ennreal-zero real)))))

(defun-sk q1191319-mutually-singular-p
    (real domain measurable left right)
  (exists (set complement)
    (and
     (q1191319-measurable-set-p measurable set)
     (q1191319-complement-set-p domain set complement)
     (q1191319-measurable-set-p measurable complement)
     (equal
      (q1191319-measure-value left set)
      (q1191319-ennreal-zero real))
     (equal
      (q1191319-measure-value right complement)
      (q1191319-ennreal-zero real)))))

;; The measure with density f has value integral (1_s f) dnu on each
;; measurable set s.

(defun-sk q1191319-restricted-density-function-p
    (real domain set density restricted)
  (forall (x)
    (and
     (q1191319-ennreal-function-p real domain restricted)
     (implies
      (q1191319-domain-member-p domain x)
      (equal
       (q1191319-function-value restricted x)
       (if (q1191319-set-member-p set x)
           (q1191319-function-value density x)
         (q1191319-ennreal-zero real)))))))

(defun-sk q1191319-with-density-value-p
    (real domain measurable base density lintegral set value)
  (exists (restricted)
    (and
     (q1191319-restricted-density-function-p
      real domain set density restricted)
     (equal
      value
      (q1191319-lintegral-value
       lintegral domain measurable base restricted)))))

(defun-sk q1191319-with-density-values-p
    (real domain measurable base density density-measure lintegral)
  (forall (set)
    (implies
     (q1191319-measurable-set-p measurable set)
     (q1191319-with-density-value-p
      real domain measurable base density lintegral set
      (q1191319-measure-value density-measure set)))))

(defun q1191319-with-density-p
    (real domain measurable base density density-measure lintegral)
  (and
   (q1191319-measure-space-p
    real domain measurable density-measure)
   (q1191319-measurable-ennreal-function-p
    real domain measurable density)
   (q1191319-with-density-values-p
    real domain measurable base density density-measure lintegral)))

;; HaveLebesgueDecomposition is the source existential package.  The
;; conservative choice below keeps the singular measure and derivative
;; internal, exactly as Lean's singularPart and rnDeriv do.

(defun q1191319-decomposition-singular-part (package)
  (nth 0 package))

(defun q1191319-decomposition-derivative (package)
  (nth 1 package))

(defun q1191319-decomposition-density-measure (package)
  (nth 2 package))

(defun q1191319-decomposition-package-p
    (real domain measurable mu nu lintegral package)
  (let ((singular-part
         (q1191319-decomposition-singular-part package))
        (derivative
         (q1191319-decomposition-derivative package))
        (density-measure
         (q1191319-decomposition-density-measure package)))
    (and
     (true-listp package)
     (equal (len package) 3)
     (q1191319-measure-space-p
      real domain measurable singular-part)
     (q1191319-with-density-p
      real domain measurable nu derivative density-measure lintegral)
     (q1191319-mutually-singular-p
      real domain measurable singular-part nu)
     (q1191319-measure-addition-p
      real measurable singular-part density-measure mu))))

(defun-sk q1191319-have-lebesgue-decomposition-p
    (real domain measurable mu nu lintegral)
  (exists (package)
    (q1191319-decomposition-package-p
     real domain measurable mu nu lintegral package)))

(defchoose q1191319-chosen-decomposition
    (package)
    (real domain measurable mu nu lintegral)
  (q1191319-decomposition-package-p
   real domain measurable mu nu lintegral package))

(defun q1191319-rn-derivative
    (real domain measurable mu nu lintegral)
  (q1191319-decomposition-derivative
   (q1191319-chosen-decomposition
    real domain measurable mu nu lintegral)))

(defun q1191319-with-density-rn-derivative
    (real domain measurable mu nu lintegral)
  (q1191319-decomposition-density-measure
   (q1191319-chosen-decomposition
    real domain measurable mu nu lintegral)))

(defun-sk thousand-theorems-q1191319-radon-nikodym-statement ()
  (forall (real domain measurable mu nu lintegral)
    (implies
     (and
      (q1191319-real-field-p real)
      (q1191319-measure-space-p
       real domain measurable mu)
      (q1191319-measure-space-p
       real domain measurable nu)
      (q1191319-lintegral-operation-p
       real domain measurable lintegral)
      (q1191319-have-lebesgue-decomposition-p
       real domain measurable mu nu lintegral))
     (iff
      (q1191319-absolutely-continuous-p
       real measurable mu nu)
      (q1191319-measure-equal-p
       domain measurable
       (q1191319-with-density-rn-derivative
        real domain measurable mu nu lintegral)
       mu)))))

(value-triple :itpeval-statement-checked)
:q
