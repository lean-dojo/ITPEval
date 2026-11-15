;; Statement-only formalization of thousand-theorems corpus artifact Q5437947,
;; "Fatou–Lebesgue theorem": for a sequence of measurable
;; extended-nonnegative-real functions on an arbitrary measure space, the
;; lower integral of the pointwise liminf is at most the liminf of the lower
;; integrals. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces reify arbitrary carriers, subsets, functions, and
;; sequences without finite enumeration or an APPLY$ restriction. Every
;; algebraic, order, measure, measurability, integral, and liminf property is
;; explicit in the statement predicates below.

(defstub q5437947-r-member-p (real value) t)
(defstub q5437947-r-zero (real) t)
(defstub q5437947-r-one (real) t)
(defstub q5437947-r-add (real left right) t)
(defstub q5437947-r-multiply (real left right) t)
(defstub q5437947-r-negate (real value) t)
(defstub q5437947-r-inverse (real value) t)
(defstub q5437947-r-less (real left right) t)
(defstub q5437947-r-set-member-p (real set value) t)
(defstub q5437947-domain-member-p (domain value) t)
(defstub q5437947-set-member-p (set value) t)
(defstub q5437947-function-value (function argument) t)
(defstub q5437947-function-sequence-value (sequence index) t)
(defstub q5437947-set-sequence-value (sequence index) t)
(defstub q5437947-measurable-set-p (measurable set) t)
(defstub q5437947-measure-value (measure set) t)
(defstub q5437947-lintegral-value
  (lintegral domain measurable measure function)
  t)

(defun q5437947-r-leq (real left right)
  (not (q5437947-r-less real right left)))

(defun-sk q5437947-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q5437947-r-member-p real x)
      (q5437947-r-member-p real y)
      (q5437947-r-member-p real z))
     (let* ((zero (q5437947-r-zero real))
            (one (q5437947-r-one real))
            (xy-add (q5437947-r-add real x y))
            (yz-add (q5437947-r-add real y z))
            (xy-mul (q5437947-r-multiply real x y))
            (yz-mul (q5437947-r-multiply real y z))
            (neg-x (q5437947-r-negate real x))
            (inv-x (q5437947-r-inverse real x)))
       (and
        (q5437947-r-member-p real xy-add)
        (q5437947-r-member-p real xy-mul)
        (q5437947-r-member-p real neg-x)
        (q5437947-r-member-p real inv-x)
        (equal
         (q5437947-r-add real xy-add z)
         (q5437947-r-add real x yz-add))
        (equal xy-add (q5437947-r-add real y x))
        (equal (q5437947-r-add real x zero) x)
        (equal (q5437947-r-add real x neg-x) zero)
        (equal
         (q5437947-r-multiply real xy-mul z)
         (q5437947-r-multiply real x yz-mul))
        (equal xy-mul (q5437947-r-multiply real y x))
        (equal (q5437947-r-multiply real x one) x)
        (equal (q5437947-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal (q5437947-r-multiply real x inv-x) one))
        (equal
         (q5437947-r-multiply
          real x (q5437947-r-add real y z))
         (q5437947-r-add
          real
          (q5437947-r-multiply real x y)
          (q5437947-r-multiply real x z))))))))

(defun-sk q5437947-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q5437947-r-member-p real x)
      (q5437947-r-member-p real y)
      (q5437947-r-member-p real z))
     (let ((zero (q5437947-r-zero real)))
       (and
        (not (q5437947-r-less real x x))
        (or
         (equal x y)
         (q5437947-r-less real x y)
         (q5437947-r-less real y x))
        (implies
         (and
          (q5437947-r-less real x y)
          (q5437947-r-less real y z))
         (q5437947-r-less real x z))
        (implies
         (q5437947-r-less real x y)
         (q5437947-r-less
          real
          (q5437947-r-add real x z)
          (q5437947-r-add real y z)))
        (implies
         (and
          (q5437947-r-less real zero x)
          (q5437947-r-less real zero y))
         (q5437947-r-less
          real zero (q5437947-r-multiply real x y))))))))

(defun-sk q5437947-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q5437947-r-member-p real x)
     (q5437947-r-set-member-p real set x))))

(defun-sk q5437947-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q5437947-r-member-p real x)
      (q5437947-r-set-member-p real set x))
     (q5437947-r-leq real x bound))))

(defun-sk q5437947-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q5437947-r-member-p real bound)
     (q5437947-r-upper-bound-p real set bound))))

(defun-sk q5437947-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q5437947-r-member-p real supremum)
     (q5437947-r-upper-bound-p real set supremum)
     (implies
      (and
       (q5437947-r-member-p real bound)
       (q5437947-r-upper-bound-p real set bound))
      (q5437947-r-leq real supremum bound)))))

(defun-sk q5437947-r-has-supremum-p (real set)
  (exists (supremum)
    (q5437947-r-supremum-p real set supremum)))

(defun-sk q5437947-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q5437947-r-set-nonempty-p real set)
      (q5437947-r-bounded-above-p real set))
     (q5437947-r-has-supremum-p real set))))

(defun q5437947-real-field-p (real)
  (let ((zero (q5437947-r-zero real))
        (one (q5437947-r-one real)))
    (and
     (q5437947-r-member-p real zero)
     (q5437947-r-member-p real one)
     (not (equal zero one))
     (q5437947-r-field-laws-p real)
     (q5437947-r-order-laws-p real)
     (q5437947-r-less real zero one)
     (q5437947-r-dedekind-complete-p real))))

(defun q5437947-ennreal-p (real value)
  (or
   (equal value :q5437947-top)
   (and
    (consp value)
    (equal (car value) :q5437947-finite)
    (q5437947-r-member-p real (cdr value))
    (q5437947-r-leq
     real (q5437947-r-zero real) (cdr value)))))

(defun q5437947-ennreal-finite (value)
  (cons :q5437947-finite value))

(defun q5437947-ennreal-zero (real)
  (q5437947-ennreal-finite (q5437947-r-zero real)))

(defun q5437947-ennreal-less (real left right)
  (cond
   ((equal left :q5437947-top) nil)
   ((equal right :q5437947-top) t)
   (t (q5437947-r-less real (cdr left) (cdr right)))))

(defun q5437947-ennreal-leq (real left right)
  (not (q5437947-ennreal-less real right left)))

(defun q5437947-ennreal-add (real left right)
  (if (or (equal left :q5437947-top)
          (equal right :q5437947-top))
      :q5437947-top
    (q5437947-ennreal-finite
     (q5437947-r-add real (cdr left) (cdr right)))))

(defun q5437947-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q5437947-ennreal-zero real))
        (equal right (q5437947-ennreal-zero real)))
    (q5437947-ennreal-zero real))
   ((or (equal left :q5437947-top)
        (equal right :q5437947-top))
    :q5437947-top)
   (t
    (q5437947-ennreal-finite
     (q5437947-r-multiply real (cdr left) (cdr right))))))

(defun-sk q5437947-valid-set-p (domain set)
  (forall (x)
    (implies
     (q5437947-set-member-p set x)
     (q5437947-domain-member-p domain x))))

(defun-sk q5437947-set-subset-p (left right)
  (forall (x)
    (implies
     (q5437947-set-member-p left x)
     (q5437947-set-member-p right x))))

(defun-sk q5437947-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q5437947-domain-member-p domain x)
     (iff
      (q5437947-set-member-p left x)
      (q5437947-set-member-p right x)))))

(defun-sk q5437947-empty-set-p (domain set)
  (forall (x)
    (iff
     (q5437947-set-member-p set x)
     (and (q5437947-domain-member-p domain x) nil))))

(defun-sk q5437947-complement-set-p (domain set complement)
  (forall (x)
    (iff
     (q5437947-set-member-p complement x)
     (and
      (q5437947-domain-member-p domain x)
      (not (q5437947-set-member-p set x))))))

(defun-sk q5437947-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q5437947-valid-set-p
      domain (q5437947-set-sequence-value sequence n)))))

(defun-sk q5437947-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q5437947-set-member-p
      (q5437947-set-sequence-value sequence n) x))))

(defun-sk q5437947-sequence-union-set-p
    (domain sequence union)
  (forall (x)
    (iff
     (q5437947-set-member-p union x)
     (and
      (q5437947-domain-member-p domain x)
      (q5437947-sequence-union-member-p sequence x)))))

(defun-sk q5437947-family-extensional-p (domain measurable)
  (forall (left right)
    (implies
     (q5437947-set-equiv-p domain left right)
     (iff
      (q5437947-measurable-set-p measurable left)
      (q5437947-measurable-set-p measurable right)))))

(defun-sk q5437947-family-valid-p (domain measurable)
  (forall (set)
    (implies
     (q5437947-measurable-set-p measurable set)
     (q5437947-valid-set-p domain set))))

(defun-sk q5437947-measurable-empty-exists-p (domain measurable)
  (exists (empty)
    (and
     (q5437947-empty-set-p domain empty)
     (q5437947-measurable-set-p measurable empty))))

(defun-sk q5437947-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q5437947-complement-set-p domain set complement)
     (q5437947-measurable-set-p measurable complement))))

(defun-sk q5437947-measurable-complements-p
    (domain measurable)
  (forall (set)
    (implies
     (q5437947-measurable-set-p measurable set)
     (q5437947-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q5437947-set-sequence-measurable-p
    (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q5437947-measurable-set-p
      measurable (q5437947-set-sequence-value sequence n)))))

(defun-sk q5437947-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q5437947-sequence-union-set-p domain sequence union)
     (q5437947-measurable-set-p measurable union))))

(defun-sk q5437947-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q5437947-set-sequence-p domain sequence)
      (q5437947-set-sequence-measurable-p measurable sequence))
     (q5437947-measurable-union-exists-p
      domain measurable sequence))))

(defun q5437947-sigma-algebra-p (domain measurable)
  (and
   (q5437947-family-extensional-p domain measurable)
   (q5437947-family-valid-p domain measurable)
   (q5437947-measurable-empty-exists-p domain measurable)
   (q5437947-measurable-complements-p domain measurable)
   (q5437947-measurable-sequence-unions-p domain measurable)))

(defun-sk q5437947-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q5437947-set-member-p left x)
      (q5437947-set-member-p right x)))))

(defun-sk q5437947-pairwise-disjoint-p (sequence)
  (forall (m n)
    (implies
     (and (natp m) (natp n) (not (equal m n)))
     (q5437947-disjoint-sets-p
      (q5437947-set-sequence-value sequence m)
      (q5437947-set-sequence-value sequence n)))))

(defun q5437947-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q5437947-ennreal-zero real)
    (q5437947-ennreal-add
     real
     (q5437947-measure-prefix-sum
      real measure sequence (1- count))
     (q5437947-measure-value
      measure (q5437947-set-sequence-value sequence (1- count))))))

(defun-sk q5437947-countable-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q5437947-ennreal-leq
      real
      (q5437947-measure-prefix-sum real measure sequence count)
      bound))))

(defun-sk q5437947-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q5437947-ennreal-p real total)
     (q5437947-countable-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q5437947-ennreal-p real bound)
       (q5437947-countable-sum-upper-bound-p
        real measure sequence bound))
      (q5437947-ennreal-leq real total bound)))))

(defun-sk q5437947-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q5437947-set-equiv-p domain left right)
     (equal
      (q5437947-measure-value measure left)
      (q5437947-measure-value measure right)))))

(defun-sk q5437947-measure-values-p (real domain measure)
  (forall (set)
    (implies
     (q5437947-valid-set-p domain set)
     (q5437947-ennreal-p
      real (q5437947-measure-value measure set)))))

(defun-sk q5437947-measure-empty-zero-p (real domain measure)
  (forall (empty)
    (implies
     (q5437947-empty-set-p domain empty)
     (equal
      (q5437947-measure-value measure empty)
      (q5437947-ennreal-zero real)))))

(defun-sk q5437947-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q5437947-set-sequence-p domain sequence)
      (q5437947-set-sequence-measurable-p measurable sequence)
      (q5437947-pairwise-disjoint-p sequence)
      (q5437947-sequence-union-set-p domain sequence union))
     (q5437947-countable-sum-p
      real measure sequence
      (q5437947-measure-value measure union)))))

(defun-sk q5437947-measurable-superset-lower-bound-p
    (real measurable measure set lower)
  (forall (superset)
    (implies
     (and
      (q5437947-measurable-set-p measurable superset)
      (q5437947-set-subset-p set superset))
     (q5437947-ennreal-leq
      real lower (q5437947-measure-value measure superset)))))

(defun-sk q5437947-outer-measure-value-p
    (real measurable measure set)
  (forall (lower)
    (and
     (q5437947-measurable-superset-lower-bound-p
      real measurable measure set
      (q5437947-measure-value measure set))
     (implies
      (and
       (q5437947-ennreal-p real lower)
       (q5437947-measurable-superset-lower-bound-p
        real measurable measure set lower))
      (q5437947-ennreal-leq
       real lower (q5437947-measure-value measure set))))))

(defun-sk q5437947-outer-measure-values-p
    (real domain measurable measure)
  (forall (set)
    (implies
     (q5437947-valid-set-p domain set)
     (q5437947-outer-measure-value-p
      real measurable measure set))))

(defun q5437947-measure-space-p
    (real domain measurable measure)
  (and
   (q5437947-sigma-algebra-p domain measurable)
   (q5437947-measure-extensional-p domain measure)
   (q5437947-measure-values-p real domain measure)
   (q5437947-measure-empty-zero-p real domain measure)
   (q5437947-countably-additive-p
    real domain measurable measure)
   (q5437947-outer-measure-values-p
    real domain measurable measure)))

(defun-sk q5437947-ennreal-function-p (real domain function)
  (forall (x)
    (implies
     (q5437947-domain-member-p domain x)
     (q5437947-ennreal-p
      real (q5437947-function-value function x)))))

(defun-sk q5437947-ennreal-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q5437947-set-member-p set x)
     (and
      (q5437947-domain-member-p domain x)
      (q5437947-ennreal-less
       real threshold (q5437947-function-value function x))))))

(defun-sk q5437947-ennreal-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q5437947-ennreal-upper-preimage-set-p
      real domain function threshold set)
     (q5437947-measurable-set-p measurable set))))

(defun-sk q5437947-measurable-ennreal-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q5437947-ennreal-function-p real domain function)
     (implies
      (q5437947-ennreal-p real threshold)
      (q5437947-ennreal-upper-preimage-exists-p
       real domain measurable function threshold)))))

;; The lower Lebesgue integral is the supremum of integrals of measurable
;; finite-range simple functions below the integrand.

(defun-sk q5437947-value-attained-p (domain function value)
  (exists (x)
    (and
     (q5437947-domain-member-p domain x)
     (equal (q5437947-function-value function x) value))))

(defun q5437947-values-attained-p (domain function values)
  (if (consp values)
      (and
       (q5437947-value-attained-p domain function (car values))
       (q5437947-values-attained-p domain function (cdr values)))
    (equal values nil)))

(defun q5437947-ennreal-value-list-p (real values)
  (if (consp values)
      (and
       (q5437947-ennreal-p real (car values))
       (q5437947-ennreal-value-list-p real (cdr values)))
    (equal values nil)))

(defun-sk q5437947-range-in-values-p (domain function values)
  (forall (x)
    (implies
     (q5437947-domain-member-p domain x)
     (member-equal
      (q5437947-function-value function x) values))))

(defun-sk q5437947-fiber-set-p (domain function value set)
  (forall (x)
    (iff
     (q5437947-set-member-p set x)
     (and
      (q5437947-domain-member-p domain x)
      (equal (q5437947-function-value function x) value)))))

(defun q5437947-fiber-list-p (domain function values fibers)
  (if (consp values)
      (and
       (consp fibers)
       (q5437947-fiber-set-p
        domain function (car values) (car fibers))
       (q5437947-fiber-list-p
        domain function (cdr values) (cdr fibers)))
    (equal fibers nil)))

(defun q5437947-finite-simple-integral
    (real measure values fibers)
  (if (consp values)
      (q5437947-ennreal-add
       real
       (q5437947-ennreal-multiply
        real
        (car values)
        (q5437947-measure-value measure (car fibers)))
       (q5437947-finite-simple-integral
        real measure (cdr values) (cdr fibers)))
    (q5437947-ennreal-zero real)))

(defun q5437947-simple-function-data-p
    (real domain measurable function values fibers)
  (and
   (true-listp values)
   (true-listp fibers)
   (no-duplicatesp-equal values)
   (q5437947-ennreal-value-list-p real values)
   (q5437947-values-attained-p domain function values)
   (q5437947-range-in-values-p domain function values)
   (q5437947-fiber-list-p domain function values fibers)
   (q5437947-measurable-ennreal-function-p
    real domain measurable function)))

(defun-sk q5437947-simple-below-p
    (real domain simple function)
  (forall (x)
    (implies
     (q5437947-domain-member-p domain x)
     (q5437947-ennreal-leq
      real
      (q5437947-function-value simple x)
      (q5437947-function-value function x)))))

(defun-sk q5437947-lintegral-upper-bound-p
    (real domain measurable measure function bound)
  (forall (simple values fibers)
    (implies
     (and
      (q5437947-simple-function-data-p
       real domain measurable simple values fibers)
      (q5437947-simple-below-p real domain simple function))
     (q5437947-ennreal-leq
      real
      (q5437947-finite-simple-integral
       real measure values fibers)
      bound))))

(defun-sk q5437947-lintegral-value-p
    (real domain measurable measure function value)
  (forall (bound)
    (and
     (q5437947-ennreal-function-p real domain function)
     (q5437947-ennreal-p real value)
     (q5437947-lintegral-upper-bound-p
      real domain measurable measure function value)
     (implies
      (and
       (q5437947-ennreal-p real bound)
       (q5437947-lintegral-upper-bound-p
        real domain measurable measure function bound))
      (q5437947-ennreal-leq real value bound)))))

(defun-sk q5437947-lintegral-operation-p
    (real domain measurable measure lintegral)
  (forall (function)
    (implies
     (q5437947-ennreal-function-p real domain function)
     (q5437947-lintegral-value-p
      real domain measurable measure function
      (q5437947-lintegral-value
       lintegral domain measurable measure function)))))

(defun-sk q5437947-ennreal-function-sequence-p
    (real domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q5437947-ennreal-function-p
      real domain
      (q5437947-function-sequence-value sequence n)))))

(defun-sk q5437947-sequence-measurable-p
    (real domain measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q5437947-measurable-ennreal-function-p
      real domain measurable
      (q5437947-function-sequence-value sequence n)))))

;; Liminf atTop is the supremum of all eventual lower bounds.

(defun-sk q5437947-pointwise-eventual-lower-from-p
    (real sequence x lower start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q5437947-ennreal-leq
      real lower
      (q5437947-function-value
       (q5437947-function-sequence-value sequence n) x)))))

(defun-sk q5437947-pointwise-eventual-lower-p
    (real sequence x lower)
  (exists (start)
    (and
     (natp start)
     (q5437947-pointwise-eventual-lower-from-p
      real sequence x lower start))))

(defun-sk q5437947-pointwise-liminf-upper-bound-p
    (real sequence x bound)
  (forall (lower)
    (implies
     (and
      (q5437947-ennreal-p real lower)
      (q5437947-pointwise-eventual-lower-p
       real sequence x lower))
     (q5437947-ennreal-leq real lower bound))))

(defun-sk q5437947-pointwise-liminf-value-p
    (real sequence x value)
  (forall (bound)
    (and
     (q5437947-ennreal-p real value)
     (q5437947-pointwise-liminf-upper-bound-p
      real sequence x value)
     (implies
      (and
       (q5437947-ennreal-p real bound)
       (q5437947-pointwise-liminf-upper-bound-p
        real sequence x bound))
      (q5437947-ennreal-leq real value bound)))))

(defun-sk q5437947-pointwise-liminf-function-p
    (real domain sequence function)
  (forall (x)
    (and
     (q5437947-ennreal-function-p real domain function)
     (implies
      (q5437947-domain-member-p domain x)
      (q5437947-pointwise-liminf-value-p
       real sequence x (q5437947-function-value function x))))))

(defun-sk q5437947-lintegral-eventual-lower-from-p
    (real domain measurable measure lintegral sequence lower start)
  (forall (n)
    (implies
     (and (natp n) (<= start n))
     (q5437947-ennreal-leq
      real lower
      (q5437947-lintegral-value
       lintegral domain measurable measure
       (q5437947-function-sequence-value sequence n))))))

(defun-sk q5437947-lintegral-eventual-lower-p
    (real domain measurable measure lintegral sequence lower)
  (exists (start)
    (and
     (natp start)
     (q5437947-lintegral-eventual-lower-from-p
      real domain measurable measure lintegral
      sequence lower start))))

(defun-sk q5437947-lintegral-liminf-upper-bound-p
    (real domain measurable measure lintegral sequence bound)
  (forall (lower)
    (implies
     (and
      (q5437947-ennreal-p real lower)
      (q5437947-lintegral-eventual-lower-p
       real domain measurable measure lintegral sequence lower))
     (q5437947-ennreal-leq real lower bound))))

(defun-sk q5437947-lintegral-liminf-value-p
    (real domain measurable measure lintegral sequence value)
  (forall (bound)
    (and
     (q5437947-ennreal-p real value)
     (q5437947-lintegral-liminf-upper-bound-p
      real domain measurable measure lintegral sequence value)
     (implies
      (and
       (q5437947-ennreal-p real bound)
       (q5437947-lintegral-liminf-upper-bound-p
        real domain measurable measure lintegral sequence bound))
      (q5437947-ennreal-leq real value bound)))))

(defun-sk q5437947-fatou-conclusion-p
    (real domain measurable measure lintegral sequence)
  (exists (pointwise-liminf integral-liminf)
    (and
     (q5437947-pointwise-liminf-function-p
      real domain sequence pointwise-liminf)
     (q5437947-lintegral-liminf-value-p
      real domain measurable measure lintegral
      sequence integral-liminf)
     (q5437947-ennreal-leq
      real
      (q5437947-lintegral-value
       lintegral domain measurable measure pointwise-liminf)
      integral-liminf))))

(defun-sk
    thousand-theorems-q5437947-fatou-lebesgue-theorem-statement
    ()
  (forall (real domain measurable measure lintegral sequence)
    (implies
     (and
      (q5437947-real-field-p real)
      (q5437947-measure-space-p
       real domain measurable measure)
      (q5437947-lintegral-operation-p
       real domain measurable measure lintegral)
      (q5437947-ennreal-function-sequence-p
       real domain sequence)
      (q5437947-sequence-measurable-p
       real domain measurable sequence))
     (q5437947-fatou-conclusion-p
      real domain measurable measure lintegral sequence))))

(value-triple :itpeval-statement-checked)
:q
