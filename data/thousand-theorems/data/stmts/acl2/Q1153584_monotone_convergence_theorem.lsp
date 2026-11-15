;; Statement-only formalization of thousand-theorems corpus artifact Q1153584,
;; "Monotone convergence theorem": lower integrals preserve almost-everywhere
;; monotone limits of extended-nonnegative-real functions, and Bochner
;; integrals preserve almost-everywhere antitone limits of integrable
;; real-valued functions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces give identifiers to arbitrary carriers, subsets,
;; functions, and sequences.  No carrier or function is replaced by a finite
;; table or restricted to an APPLY$ class.  The hypotheses below characterize
;; the real field, sigma algebra, measure, lower integral, real integral,
;; almost-everywhere predicates, and order-topological convergence exactly.

;; Real numbers and arbitrary mathematical objects.

(defstub q1153584-r-member-p (real value) t)
(defstub q1153584-r-zero (real) t)
(defstub q1153584-r-one (real) t)
(defstub q1153584-r-add (real left right) t)
(defstub q1153584-r-multiply (real left right) t)
(defstub q1153584-r-negate (real value) t)
(defstub q1153584-r-inverse (real value) t)
(defstub q1153584-r-less (real left right) t)
(defstub q1153584-r-set-member-p (real set value) t)

(defstub q1153584-domain-member-p (domain value) t)
(defstub q1153584-set-member-p (set value) t)
(defstub q1153584-function-value (function argument) t)
(defstub q1153584-function-sequence-value (sequence index) t)
(defstub q1153584-set-sequence-value (sequence index) t)
(defstub q1153584-measurable-set-p (measurable set) t)
(defstub q1153584-measure-value (measure set) t)
(defstub q1153584-lintegral-value
  (lintegral domain measurable measure function) t)
(defstub q1153584-integral-value
  (integral real domain measurable measure lintegral function) t)

(defun q1153584-r-leq (real left right)
  (not (q1153584-r-less real right left)))

(defun q1153584-r-abs (real value)
  (if (q1153584-r-less real value (q1153584-r-zero real))
      (q1153584-r-negate real value)
    value))

(defun-sk q1153584-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1153584-r-member-p real x)
      (q1153584-r-member-p real y)
      (q1153584-r-member-p real z))
     (let* ((zero (q1153584-r-zero real))
            (one (q1153584-r-one real))
            (xy-add (q1153584-r-add real x y))
            (yz-add (q1153584-r-add real y z))
            (xy-mul (q1153584-r-multiply real x y))
            (yz-mul (q1153584-r-multiply real y z))
            (neg-x (q1153584-r-negate real x))
            (inv-x (q1153584-r-inverse real x)))
       (and
        (q1153584-r-member-p real xy-add)
        (q1153584-r-member-p real xy-mul)
        (q1153584-r-member-p real neg-x)
        (q1153584-r-member-p real inv-x)
        (equal
         (q1153584-r-add real xy-add z)
         (q1153584-r-add real x yz-add))
        (equal xy-add (q1153584-r-add real y x))
        (equal (q1153584-r-add real x zero) x)
        (equal (q1153584-r-add real x neg-x) zero)
        (equal
         (q1153584-r-multiply real xy-mul z)
         (q1153584-r-multiply real x yz-mul))
        (equal xy-mul (q1153584-r-multiply real y x))
        (equal (q1153584-r-multiply real x one) x)
        (equal (q1153584-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1153584-r-multiply real x inv-x)
          one))
        (equal
         (q1153584-r-multiply
          real x (q1153584-r-add real y z))
         (q1153584-r-add
          real
          (q1153584-r-multiply real x y)
          (q1153584-r-multiply real x z))))))))

(defun-sk q1153584-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1153584-r-member-p real x)
      (q1153584-r-member-p real y)
      (q1153584-r-member-p real z))
     (let ((zero (q1153584-r-zero real)))
       (and
        (not (q1153584-r-less real x x))
        (or
         (equal x y)
         (q1153584-r-less real x y)
         (q1153584-r-less real y x))
        (implies
         (and
          (q1153584-r-less real x y)
          (q1153584-r-less real y z))
         (q1153584-r-less real x z))
        (implies
         (q1153584-r-less real x y)
         (q1153584-r-less
          real
          (q1153584-r-add real x z)
          (q1153584-r-add real y z)))
        (implies
         (and
          (q1153584-r-less real zero x)
          (q1153584-r-less real zero y))
         (q1153584-r-less
          real zero
          (q1153584-r-multiply real x y))))))))

(defun-sk q1153584-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q1153584-r-member-p real x)
     (q1153584-r-set-member-p real set x))))

(defun-sk q1153584-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q1153584-r-member-p real x)
      (q1153584-r-set-member-p real set x))
     (q1153584-r-leq real x bound))))

(defun-sk q1153584-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q1153584-r-member-p real bound)
     (q1153584-r-upper-bound-p real set bound))))

(defun-sk q1153584-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q1153584-r-member-p real supremum)
     (q1153584-r-upper-bound-p real set supremum)
     (implies
      (and
       (q1153584-r-member-p real bound)
       (q1153584-r-upper-bound-p real set bound))
      (q1153584-r-leq real supremum bound)))))

(defun-sk q1153584-r-has-supremum-p (real set)
  (exists (supremum)
    (q1153584-r-supremum-p real set supremum)))

(defun-sk q1153584-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q1153584-r-set-nonempty-p real set)
      (q1153584-r-bounded-above-p real set))
     (q1153584-r-has-supremum-p real set))))

(defun q1153584-real-field-p (real)
  (let ((zero (q1153584-r-zero real))
        (one (q1153584-r-one real)))
    (and
     (q1153584-r-member-p real zero)
     (q1153584-r-member-p real one)
     (not (equal zero one))
     (q1153584-r-field-laws-p real)
     (q1153584-r-order-laws-p real)
     (q1153584-r-less real zero one)
     (q1153584-r-dedekind-complete-p real))))

;; Extended nonnegative reals.

(defun q1153584-ennreal-p (real value)
  (or
   (equal value :q1153584-top)
   (and
    (consp value)
    (equal (car value) :q1153584-finite)
    (q1153584-r-member-p real (cdr value))
    (q1153584-r-leq
     real (q1153584-r-zero real) (cdr value)))))

(defun q1153584-ennreal-finite (value)
  (cons :q1153584-finite value))

(defun q1153584-ennreal-zero (real)
  (q1153584-ennreal-finite (q1153584-r-zero real)))

(defun q1153584-ennreal-less (real left right)
  (cond
   ((equal left :q1153584-top) nil)
   ((equal right :q1153584-top) t)
   (t (q1153584-r-less real (cdr left) (cdr right)))))

(defun q1153584-ennreal-leq (real left right)
  (not (q1153584-ennreal-less real right left)))

(defun q1153584-ennreal-add (real left right)
  (if (or (equal left :q1153584-top)
          (equal right :q1153584-top))
      :q1153584-top
    (q1153584-ennreal-finite
     (q1153584-r-add real (cdr left) (cdr right)))))

(defun q1153584-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q1153584-ennreal-zero real))
        (equal right (q1153584-ennreal-zero real)))
    (q1153584-ennreal-zero real))
   ((or (equal left :q1153584-top)
        (equal right :q1153584-top))
    :q1153584-top)
   (t
    (q1153584-ennreal-finite
     (q1153584-r-multiply real (cdr left) (cdr right))))))

(defun q1153584-ennreal-to-real (real value)
  (if (and (consp value)
           (equal (car value) :q1153584-finite))
      (cdr value)
    (q1153584-r-zero real)))

;; Sets, sigma algebras, and measures.

(defun-sk q1153584-valid-set-p (domain set)
  (forall (x)
    (implies
     (q1153584-set-member-p set x)
     (q1153584-domain-member-p domain x))))

(defun-sk q1153584-set-subset-p (left right)
  (forall (x)
    (implies
     (q1153584-set-member-p left x)
     (q1153584-set-member-p right x))))

(defun-sk q1153584-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q1153584-domain-member-p domain x)
     (iff
      (q1153584-set-member-p left x)
      (q1153584-set-member-p right x)))))

(defun-sk q1153584-empty-set-p (domain set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and (q1153584-domain-member-p domain x) nil))))

(defun-sk q1153584-complement-set-p (domain set complement)
  (forall (x)
    (iff
     (q1153584-set-member-p complement x)
     (and
      (q1153584-domain-member-p domain x)
      (not (q1153584-set-member-p set x))))))

(defun-sk q1153584-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q1153584-valid-set-p
      domain
      (q1153584-set-sequence-value sequence n)))))

(defun-sk q1153584-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q1153584-set-member-p
      (q1153584-set-sequence-value sequence n)
      x))))

(defun-sk q1153584-sequence-union-set-p
    (domain sequence union)
  (forall (x)
    (iff
     (q1153584-set-member-p union x)
     (and
      (q1153584-domain-member-p domain x)
      (q1153584-sequence-union-member-p sequence x)))))

(defun-sk q1153584-family-extensional-p (domain measurable)
  (forall (left right)
    (implies
     (q1153584-set-equiv-p domain left right)
     (iff
      (q1153584-measurable-set-p measurable left)
      (q1153584-measurable-set-p measurable right)))))

(defun-sk q1153584-family-valid-p (domain measurable)
  (forall (set)
    (implies
     (q1153584-measurable-set-p measurable set)
     (q1153584-valid-set-p domain set))))

(defun-sk q1153584-measurable-empty-exists-p (domain measurable)
  (exists (empty)
    (and
     (q1153584-empty-set-p domain empty)
     (q1153584-measurable-set-p measurable empty))))

(defun-sk q1153584-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q1153584-complement-set-p domain set complement)
     (q1153584-measurable-set-p measurable complement))))

(defun-sk q1153584-measurable-complements-p
    (domain measurable)
  (forall (set)
    (implies
     (q1153584-measurable-set-p measurable set)
     (q1153584-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q1153584-sequence-measurable-p (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q1153584-measurable-set-p
      measurable
      (q1153584-set-sequence-value sequence n)))))

(defun-sk q1153584-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q1153584-sequence-union-set-p domain sequence union)
     (q1153584-measurable-set-p measurable union))))

(defun-sk q1153584-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q1153584-set-sequence-p domain sequence)
      (q1153584-sequence-measurable-p measurable sequence))
     (q1153584-measurable-union-exists-p
      domain measurable sequence))))

(defun q1153584-sigma-algebra-p (domain measurable)
  (and
   (q1153584-family-extensional-p domain measurable)
   (q1153584-family-valid-p domain measurable)
   (q1153584-measurable-empty-exists-p domain measurable)
   (q1153584-measurable-complements-p domain measurable)
   (q1153584-measurable-sequence-unions-p domain measurable)))

(defun-sk q1153584-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q1153584-set-member-p left x)
      (q1153584-set-member-p right x)))))

(defun-sk q1153584-pairwise-disjoint-p (sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (q1153584-disjoint-sets-p
      (q1153584-set-sequence-value sequence m)
      (q1153584-set-sequence-value sequence n)))))

(defun q1153584-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1153584-ennreal-zero real)
    (q1153584-ennreal-add
     real
     (q1153584-measure-prefix-sum
      real measure sequence (1- count))
     (q1153584-measure-value
      measure
      (q1153584-set-sequence-value sequence (1- count))))))

(defun-sk q1153584-countable-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q1153584-ennreal-leq
      real
      (q1153584-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q1153584-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q1153584-ennreal-p real total)
     (q1153584-countable-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q1153584-ennreal-p real bound)
       (q1153584-countable-sum-upper-bound-p
        real measure sequence bound))
      (q1153584-ennreal-leq real total bound)))))

(defun-sk q1153584-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q1153584-set-equiv-p domain left right)
     (equal
      (q1153584-measure-value measure left)
      (q1153584-measure-value measure right)))))

(defun-sk q1153584-measure-values-p (real domain measure)
  (forall (set)
    (implies
     (q1153584-valid-set-p domain set)
     (q1153584-ennreal-p
      real (q1153584-measure-value measure set)))))

(defun-sk q1153584-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q1153584-empty-set-p domain empty)
     (equal
      (q1153584-measure-value measure empty)
      (q1153584-ennreal-zero real)))))

(defun-sk q1153584-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q1153584-set-sequence-p domain sequence)
      (q1153584-sequence-measurable-p measurable sequence)
      (q1153584-pairwise-disjoint-p sequence)
      (q1153584-sequence-union-set-p domain sequence union))
     (q1153584-countable-sum-p
      real measure sequence
      (q1153584-measure-value measure union)))))

(defun-sk q1153584-measurable-superset-lower-bound-p
    (real measurable measure set lower)
  (forall (superset)
    (implies
     (and
      (q1153584-measurable-set-p measurable superset)
      (q1153584-set-subset-p set superset))
     (q1153584-ennreal-leq
      real lower
      (q1153584-measure-value measure superset)))))

(defun-sk q1153584-outer-measure-value-p
    (real measurable measure set)
  (forall (lower)
    (and
     (q1153584-measurable-superset-lower-bound-p
      real measurable measure set
      (q1153584-measure-value measure set))
     (implies
      (and
       (q1153584-ennreal-p real lower)
       (q1153584-measurable-superset-lower-bound-p
        real measurable measure set lower))
      (q1153584-ennreal-leq
       real lower
       (q1153584-measure-value measure set))))))

(defun-sk q1153584-outer-measure-values-p
    (real domain measurable measure)
  (forall (set)
    (implies
     (q1153584-valid-set-p domain set)
     (q1153584-outer-measure-value-p
      real measurable measure set))))

(defun q1153584-measure-space-p
    (real domain measurable measure)
  (and
   (q1153584-sigma-algebra-p domain measurable)
   (q1153584-measure-extensional-p domain measure)
   (q1153584-measure-values-p real domain measure)
   (q1153584-measure-empty-zero-p real domain measure)
   (q1153584-countably-additive-p
    real domain measurable measure)
   (q1153584-outer-measure-values-p
    real domain measurable measure)))

(defun q1153584-null-set-p (real domain measure set)
  (and
   (q1153584-valid-set-p domain set)
   (equal
    (q1153584-measure-value measure set)
    (q1153584-ennreal-zero real))))

;; Typed functions and measurability through upper-ray preimages.

(defun-sk q1153584-real-function-p (real domain function)
  (forall (x)
    (implies
     (q1153584-domain-member-p domain x)
     (q1153584-r-member-p
      real (q1153584-function-value function x)))))

(defun-sk q1153584-ennreal-function-p (real domain function)
  (forall (x)
    (implies
     (q1153584-domain-member-p domain x)
     (q1153584-ennreal-p
      real (q1153584-function-value function x)))))

(defun-sk q1153584-real-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (q1153584-r-less
       real threshold
       (q1153584-function-value function x))))))

(defun-sk q1153584-ennreal-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (q1153584-ennreal-less
       real threshold
       (q1153584-function-value function x))))))

(defun-sk q1153584-real-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q1153584-real-upper-preimage-set-p
      real domain function threshold set)
     (q1153584-measurable-set-p measurable set))))

(defun-sk q1153584-ennreal-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q1153584-ennreal-upper-preimage-set-p
      real domain function threshold set)
     (q1153584-measurable-set-p measurable set))))

(defun-sk q1153584-measurable-real-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q1153584-real-function-p real domain function)
     (implies
      (q1153584-r-member-p real threshold)
      (q1153584-real-upper-preimage-exists-p
       real domain measurable function threshold)))))

(defun-sk q1153584-measurable-ennreal-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q1153584-ennreal-function-p real domain function)
     (implies
      (q1153584-ennreal-p real threshold)
      (q1153584-ennreal-upper-preimage-exists-p
       real domain measurable function threshold)))))

(defun-sk q1153584-disagreement-set-p
    (domain left right set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (not
       (equal
        (q1153584-function-value left x)
        (q1153584-function-value right x)))))))

(defun-sk q1153584-ae-equal-p
    (real domain measure left right)
  (exists (set)
    (and
     (q1153584-disagreement-set-p domain left right set)
     (q1153584-null-set-p real domain measure set))))

(defun-sk q1153584-ae-real-measurable-p
    (real domain measurable measure function)
  (exists (representative)
    (and
     (q1153584-real-function-p real domain function)
     (q1153584-measurable-real-function-p
      real domain measurable representative)
     (q1153584-ae-equal-p
      real domain measure function representative))))

(defun-sk q1153584-ae-ennreal-measurable-p
    (real domain measurable measure function)
  (exists (representative)
    (and
     (q1153584-ennreal-function-p real domain function)
     (q1153584-measurable-ennreal-function-p
      real domain measurable representative)
     (q1153584-ae-equal-p
      real domain measure function representative))))

;; The lower Lebesgue integral as the supremum of measurable finite-range
;; simple functions below the integrand.

(defun-sk q1153584-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q1153584-domain-member-p domain x)
     (equal
      (q1153584-function-value function x)
      value))))

(defun q1153584-values-attained-p
    (domain function values)
  (if (consp values)
      (and
       (q1153584-value-attained-p
        domain function (car values))
       (q1153584-values-attained-p
        domain function (cdr values)))
    (equal values nil)))

(defun q1153584-ennreal-value-list-p (real values)
  (if (consp values)
      (and
       (q1153584-ennreal-p real (car values))
       (q1153584-ennreal-value-list-p real (cdr values)))
    (equal values nil)))

(defun-sk q1153584-range-in-values-p
    (domain function values)
  (forall (x)
    (implies
     (q1153584-domain-member-p domain x)
     (member-equal
      (q1153584-function-value function x)
      values))))

(defun-sk q1153584-fiber-set-p
    (domain function value set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (equal
       (q1153584-function-value function x)
       value)))))

(defun q1153584-fiber-list-p
    (domain function values fibers)
  (if (consp values)
      (and
       (consp fibers)
       (q1153584-fiber-set-p
        domain function (car values) (car fibers))
       (q1153584-fiber-list-p
        domain function (cdr values) (cdr fibers)))
    (equal fibers nil)))

(defun q1153584-finite-simple-integral
    (real measure values fibers)
  (if (consp values)
      (q1153584-ennreal-add
       real
       (q1153584-ennreal-multiply
        real
        (car values)
        (q1153584-measure-value measure (car fibers)))
       (q1153584-finite-simple-integral
        real measure (cdr values) (cdr fibers)))
    (q1153584-ennreal-zero real)))

(defun q1153584-simple-function-data-p
    (real domain measurable function values fibers)
  (and
   (true-listp values)
   (true-listp fibers)
   (no-duplicatesp-equal values)
   (q1153584-ennreal-value-list-p real values)
   (q1153584-values-attained-p domain function values)
   (q1153584-range-in-values-p domain function values)
   (q1153584-fiber-list-p domain function values fibers)
   (q1153584-measurable-ennreal-function-p
    real domain measurable function)))

(defun-sk q1153584-simple-below-p
    (real domain simple function)
  (forall (x)
    (implies
     (q1153584-domain-member-p domain x)
     (q1153584-ennreal-leq
      real
      (q1153584-function-value simple x)
      (q1153584-function-value function x)))))

(defun-sk q1153584-lintegral-upper-bound-p
    (real domain measurable measure function bound)
  (forall (simple values fibers)
    (implies
     (and
      (q1153584-simple-function-data-p
       real domain measurable simple values fibers)
      (q1153584-simple-below-p
       real domain simple function))
     (q1153584-ennreal-leq
      real
      (q1153584-finite-simple-integral
       real measure values fibers)
      bound))))

(defun-sk q1153584-lintegral-value-p
    (real domain measurable measure function value)
  (forall (bound)
    (and
     (q1153584-ennreal-function-p real domain function)
     (q1153584-ennreal-p real value)
     (q1153584-lintegral-upper-bound-p
      real domain measurable measure function value)
     (implies
      (and
       (q1153584-ennreal-p real bound)
       (q1153584-lintegral-upper-bound-p
        real domain measurable measure function bound))
      (q1153584-ennreal-leq real value bound)))))

(defun-sk q1153584-lintegral-operation-p
    (real domain measurable measure lintegral)
  (forall (function)
    (implies
     (q1153584-ennreal-function-p real domain function)
     (q1153584-lintegral-value-p
      real domain measurable measure function
      (q1153584-lintegral-value
       lintegral domain measurable measure function)))))

;; The real Bochner integral, specialized to real-valued functions.

(defun-sk q1153584-enorm-function-p
    (real domain function enorm-function)
  (forall (x)
    (and
     (q1153584-ennreal-function-p real domain enorm-function)
     (implies
      (q1153584-domain-member-p domain x)
      (equal
       (q1153584-function-value enorm-function x)
       (q1153584-ennreal-finite
        (q1153584-r-abs
         real
         (q1153584-function-value function x))))))))

(defun-sk q1153584-integrable-enorm-exists-p
    (real domain measurable measure lintegral function)
  (exists (enorm-function)
    (and
     (q1153584-enorm-function-p
      real domain function enorm-function)
     (q1153584-ennreal-less
      real
      (q1153584-lintegral-value
       lintegral domain measurable measure enorm-function)
      :q1153584-top))))

(defun q1153584-integrable-p
    (real domain measurable measure lintegral function)
  (and
   (q1153584-ae-real-measurable-p
    real domain measurable measure function)
   (q1153584-integrable-enorm-exists-p
    real domain measurable measure lintegral function)))

(defun-sk q1153584-positive-part-function-p
    (real domain function positive)
  (forall (x)
    (and
     (q1153584-ennreal-function-p real domain positive)
     (implies
      (q1153584-domain-member-p domain x)
      (equal
       (q1153584-function-value positive x)
       (q1153584-ennreal-finite
        (if
            (q1153584-r-less
             real
             (q1153584-function-value function x)
             (q1153584-r-zero real))
            (q1153584-r-zero real)
          (q1153584-function-value function x))))))))

(defun-sk q1153584-negative-part-function-p
    (real domain function negative)
  (forall (x)
    (and
     (q1153584-ennreal-function-p real domain negative)
     (implies
      (q1153584-domain-member-p domain x)
      (let ((negated
             (q1153584-r-negate
              real
              (q1153584-function-value function x))))
        (equal
         (q1153584-function-value negative x)
         (q1153584-ennreal-finite
          (if
              (q1153584-r-less
               real negated (q1153584-r-zero real))
              (q1153584-r-zero real)
            negated))))))))

(defun-sk q1153584-real-integral-witness-exists-p
    (integral real domain measurable measure lintegral function value)
  (exists (positive negative)
    (and
     (q1153584-positive-part-function-p
      real domain function positive)
     (q1153584-negative-part-function-p
      real domain function negative)
     (equal
      value
      (q1153584-r-add
       real
       (q1153584-ennreal-to-real
        real
        (q1153584-lintegral-value
         lintegral domain measurable measure positive))
       (q1153584-r-negate
        real
        (q1153584-ennreal-to-real
         real
         (q1153584-lintegral-value
          lintegral domain measurable measure negative))))))))

(defun q1153584-real-integral-value-p
    (integral real domain measurable measure lintegral function value)
  (and
   (q1153584-r-member-p real value)
   (if
       (q1153584-integrable-p
        real domain measurable measure lintegral function)
       (q1153584-real-integral-witness-exists-p
        integral real domain measurable measure
        lintegral function value)
     (equal value (q1153584-r-zero real)))))

(defun-sk q1153584-real-integral-operation-p
    (integral real domain measurable measure lintegral)
  (forall (function)
    (implies
     (q1153584-real-function-p real domain function)
     (q1153584-real-integral-value-p
      integral real domain measurable measure lintegral function
      (q1153584-integral-value
       integral real domain measurable measure
       lintegral function)))))

;; Almost-everywhere monotonicity and pointwise convergence.

(defun-sk q1153584-pointwise-ennreal-monotone-p
    (real sequence x)
  (forall (n m)
    (implies
     (and (natp n) (natp m) (<= n m))
     (q1153584-ennreal-leq
      real
      (q1153584-function-value
       (q1153584-function-sequence-value sequence n) x)
      (q1153584-function-value
       (q1153584-function-sequence-value sequence m) x)))))

(defun-sk q1153584-pointwise-real-antitone-p
    (real sequence x)
  (forall (n m)
    (implies
     (and (natp n) (natp m) (<= n m))
     (q1153584-r-leq
      real
      (q1153584-function-value
       (q1153584-function-sequence-value sequence m) x)
      (q1153584-function-value
       (q1153584-function-sequence-value sequence n) x)))))

(defun-sk q1153584-ennreal-monotone-failure-set-p
    (real domain sequence set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (not
       (q1153584-pointwise-ennreal-monotone-p
        real sequence x))))))

(defun-sk q1153584-real-antitone-failure-set-p
    (real domain sequence set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (not
       (q1153584-pointwise-real-antitone-p
        real sequence x))))))

(defun-sk q1153584-ae-ennreal-monotone-p
    (real domain measure sequence)
  (exists (set)
    (and
     (q1153584-ennreal-monotone-failure-set-p
      real domain sequence set)
     (q1153584-null-set-p real domain measure set))))

(defun-sk q1153584-ae-real-antitone-p
    (real domain measure sequence)
  (exists (set)
    (and
     (q1153584-real-antitone-failure-set-p
      real domain sequence set)
     (q1153584-null-set-p real domain measure set))))

(defun-sk q1153584-pointwise-ennreal-eventually-above-from-p
    (real sequence x lower start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-ennreal-less
      real lower
      (q1153584-function-value
       (q1153584-function-sequence-value sequence n) x)))))

(defun-sk q1153584-pointwise-ennreal-eventually-above-p
    (real sequence x lower)
  (exists (start)
    (and
     (natp start)
     (q1153584-pointwise-ennreal-eventually-above-from-p
      real sequence x lower start))))

(defun-sk q1153584-pointwise-ennreal-eventually-below-from-p
    (real sequence x upper start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-ennreal-less
      real
      (q1153584-function-value
       (q1153584-function-sequence-value sequence n) x)
      upper))))

(defun-sk q1153584-pointwise-ennreal-eventually-below-p
    (real sequence x upper)
  (exists (start)
    (and
     (natp start)
     (q1153584-pointwise-ennreal-eventually-below-from-p
      real sequence x upper start))))

(defun-sk q1153584-pointwise-ennreal-tendsto-p
    (real sequence limit x)
  (forall (bound)
    (implies
     (q1153584-ennreal-p real bound)
     (and
      (implies
       (q1153584-ennreal-less
        real bound
        (q1153584-function-value limit x))
       (q1153584-pointwise-ennreal-eventually-above-p
        real sequence x bound))
      (implies
       (q1153584-ennreal-less
        real
        (q1153584-function-value limit x)
        bound)
       (q1153584-pointwise-ennreal-eventually-below-p
        real sequence x bound))))))

(defun-sk q1153584-pointwise-real-eventually-above-from-p
    (real sequence x lower start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-r-less
      real lower
      (q1153584-function-value
       (q1153584-function-sequence-value sequence n) x)))))

(defun-sk q1153584-pointwise-real-eventually-above-p
    (real sequence x lower)
  (exists (start)
    (and
     (natp start)
     (q1153584-pointwise-real-eventually-above-from-p
      real sequence x lower start))))

(defun-sk q1153584-pointwise-real-eventually-below-from-p
    (real sequence x upper start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-r-less
      real
      (q1153584-function-value
       (q1153584-function-sequence-value sequence n) x)
      upper))))

(defun-sk q1153584-pointwise-real-eventually-below-p
    (real sequence x upper)
  (exists (start)
    (and
     (natp start)
     (q1153584-pointwise-real-eventually-below-from-p
      real sequence x upper start))))

(defun-sk q1153584-pointwise-real-tendsto-p
    (real sequence limit x)
  (forall (bound)
    (implies
     (q1153584-r-member-p real bound)
     (and
      (implies
       (q1153584-r-less
        real bound
        (q1153584-function-value limit x))
       (q1153584-pointwise-real-eventually-above-p
        real sequence x bound))
      (implies
       (q1153584-r-less
        real
        (q1153584-function-value limit x)
        bound)
       (q1153584-pointwise-real-eventually-below-p
        real sequence x bound))))))

(defun-sk q1153584-ennreal-tendsto-failure-set-p
    (real domain sequence limit set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (not
       (q1153584-pointwise-ennreal-tendsto-p
        real sequence limit x))))))

(defun-sk q1153584-real-tendsto-failure-set-p
    (real domain sequence limit set)
  (forall (x)
    (iff
     (q1153584-set-member-p set x)
     (and
      (q1153584-domain-member-p domain x)
      (not
       (q1153584-pointwise-real-tendsto-p
        real sequence limit x))))))

(defun-sk q1153584-ae-ennreal-pointwise-tendsto-p
    (real domain measure sequence limit)
  (exists (set)
    (and
     (q1153584-ennreal-tendsto-failure-set-p
      real domain sequence limit set)
     (q1153584-null-set-p real domain measure set))))

(defun-sk q1153584-ae-real-pointwise-tendsto-p
    (real domain measure sequence limit)
  (exists (set)
    (and
     (q1153584-real-tendsto-failure-set-p
      real domain sequence limit set)
     (q1153584-null-set-p real domain measure set))))

(defun-sk q1153584-ennreal-function-sequence-p
    (real domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q1153584-ennreal-function-p
      real domain
      (q1153584-function-sequence-value sequence n)))))

(defun-sk q1153584-real-function-sequence-p
    (real domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q1153584-real-function-p
      real domain
      (q1153584-function-sequence-value sequence n)))))

(defun-sk q1153584-sequence-ae-ennreal-measurable-p
    (real domain measurable measure sequence)
  (forall (n)
    (implies
     (natp n)
     (q1153584-ae-ennreal-measurable-p
      real domain measurable measure
      (q1153584-function-sequence-value sequence n)))))

(defun-sk q1153584-sequence-integrable-p
    (real domain measurable measure lintegral sequence)
  (forall (n)
    (implies
     (natp n)
     (q1153584-integrable-p
      real domain measurable measure lintegral
      (q1153584-function-sequence-value sequence n)))))

;; Convergence of the two sequences of integral values.

(defun-sk q1153584-lintegral-eventually-above-from-p
    (real domain measurable measure lintegral sequence lower start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-ennreal-less
      real lower
      (q1153584-lintegral-value
       lintegral domain measurable measure
       (q1153584-function-sequence-value sequence n))))))

(defun-sk q1153584-lintegral-eventually-above-p
    (real domain measurable measure lintegral sequence lower)
  (exists (start)
    (and
     (natp start)
     (q1153584-lintegral-eventually-above-from-p
      real domain measurable measure lintegral
      sequence lower start))))

(defun-sk q1153584-lintegral-eventually-below-from-p
    (real domain measurable measure lintegral sequence upper start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-ennreal-less
      real
      (q1153584-lintegral-value
       lintegral domain measurable measure
       (q1153584-function-sequence-value sequence n))
      upper))))

(defun-sk q1153584-lintegral-eventually-below-p
    (real domain measurable measure lintegral sequence upper)
  (exists (start)
    (and
     (natp start)
     (q1153584-lintegral-eventually-below-from-p
      real domain measurable measure lintegral
      sequence upper start))))

(defun-sk q1153584-lintegral-sequence-tendsto-p
    (real domain measurable measure lintegral sequence limit)
  (forall (bound)
    (let ((limit-value
           (q1153584-lintegral-value
            lintegral domain measurable measure limit)))
      (implies
       (q1153584-ennreal-p real bound)
       (and
        (implies
         (q1153584-ennreal-less real bound limit-value)
         (q1153584-lintegral-eventually-above-p
          real domain measurable measure lintegral
          sequence bound))
        (implies
         (q1153584-ennreal-less real limit-value bound)
         (q1153584-lintegral-eventually-below-p
          real domain measurable measure lintegral
          sequence bound)))))))

(defun-sk q1153584-integral-eventually-above-from-p
    (integral real domain measurable measure lintegral
     sequence lower start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-r-less
      real lower
      (q1153584-integral-value
       integral real domain measurable measure lintegral
       (q1153584-function-sequence-value sequence n))))))

(defun-sk q1153584-integral-eventually-above-p
    (integral real domain measurable measure lintegral sequence lower)
  (exists (start)
    (and
     (natp start)
     (q1153584-integral-eventually-above-from-p
      integral real domain measurable measure lintegral
      sequence lower start))))

(defun-sk q1153584-integral-eventually-below-from-p
    (integral real domain measurable measure lintegral
     sequence upper start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q1153584-r-less
      real
      (q1153584-integral-value
       integral real domain measurable measure lintegral
       (q1153584-function-sequence-value sequence n))
      upper))))

(defun-sk q1153584-integral-eventually-below-p
    (integral real domain measurable measure lintegral sequence upper)
  (exists (start)
    (and
     (natp start)
     (q1153584-integral-eventually-below-from-p
      integral real domain measurable measure lintegral
      sequence upper start))))

(defun-sk q1153584-integral-sequence-tendsto-p
    (integral real domain measurable measure lintegral sequence limit)
  (forall (bound)
    (let ((limit-value
           (q1153584-integral-value
            integral real domain measurable measure lintegral limit)))
      (implies
       (q1153584-r-member-p real bound)
       (and
        (implies
         (q1153584-r-less real bound limit-value)
         (q1153584-integral-eventually-above-p
          integral real domain measurable measure lintegral
          sequence bound))
        (implies
         (q1153584-r-less real limit-value bound)
         (q1153584-integral-eventually-below-p
          integral real domain measurable measure lintegral
          sequence bound)))))))

;; The two indexed statements.

(defun q1153584-lintegral-monotone-convergence-statement
    (real domain measurable measure lintegral sequence limit)
  (implies
   (and
    (q1153584-real-field-p real)
    (q1153584-measure-space-p real domain measurable measure)
    (q1153584-lintegral-operation-p
     real domain measurable measure lintegral)
    (q1153584-ennreal-function-sequence-p
     real domain sequence)
    (q1153584-ennreal-function-p real domain limit)
    (q1153584-sequence-ae-ennreal-measurable-p
     real domain measurable measure sequence)
    (q1153584-ae-ennreal-monotone-p
     real domain measure sequence)
    (q1153584-ae-ennreal-pointwise-tendsto-p
     real domain measure sequence limit))
   (q1153584-lintegral-sequence-tendsto-p
    real domain measurable measure lintegral sequence limit)))

(defun q1153584-integral-antitone-convergence-statement
    (integral real domain measurable measure lintegral sequence limit)
  (implies
   (and
    (q1153584-real-field-p real)
    (q1153584-measure-space-p real domain measurable measure)
    (q1153584-lintegral-operation-p
     real domain measurable measure lintegral)
    (q1153584-real-integral-operation-p
     integral real domain measurable measure lintegral)
    (q1153584-real-function-sequence-p real domain sequence)
    (q1153584-real-function-p real domain limit)
    (q1153584-sequence-integrable-p
     real domain measurable measure lintegral sequence)
    (q1153584-integrable-p
     real domain measurable measure lintegral limit)
    (q1153584-ae-real-antitone-p
     real domain measure sequence)
    (q1153584-ae-real-pointwise-tendsto-p
     real domain measure sequence limit))
   (q1153584-integral-sequence-tendsto-p
    integral real domain measurable measure lintegral
    sequence limit)))

(defun-sk
    thousand-theorems-q1153584-monotone-convergence-theorem-statement
    ()
  (forall
      (real domain measurable measure lintegral integral
       ennreal-sequence ennreal-limit real-sequence real-limit)
    (and
     (q1153584-lintegral-monotone-convergence-statement
      real domain measurable measure lintegral
      ennreal-sequence ennreal-limit)
     (q1153584-integral-antitone-convergence-statement
      integral real domain measurable measure lintegral
      real-sequence real-limit))))

(value-triple :itpeval-statement-checked)
:q
