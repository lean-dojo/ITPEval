;; Statement-only formalization of thousand-theorems corpus artifact Q191693,
;; "Lebesgue's decomposition theorem": on an arbitrary measurable space, every
;; s-finite measure has a decomposition relative to every sigma-finite measure
;; into a mutually singular measure and a measure with measurable density.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The conservative interfaces below range over unrestricted ACL2 objects.
;; Their laws explicitly present a complete ordered real field, extended
;; nonnegative reals, arbitrary sets and functions, a sigma algebra,
;; countably additive measures, and the lower Lebesgue integral.  S-finiteness
;; is represented by a countable sum of finite measures, sigma-finiteness by a
;; countable measurable finite-measure cover, and both decomposition witnesses
;; remain internally existential.

;; Real scalars and arbitrary mathematical objects.

(defstub q191693-r-member-p (real value) t)
(defstub q191693-r-zero (real) t)
(defstub q191693-r-one (real) t)
(defstub q191693-r-add (real left right) t)
(defstub q191693-r-multiply (real left right) t)
(defstub q191693-r-negate (real value) t)
(defstub q191693-r-inverse (real value) t)
(defstub q191693-r-less (real left right) t)
(defstub q191693-r-set-member-p (real set value) t)

(defstub q191693-domain-member-p (domain value) t)
(defstub q191693-set-member-p (set value) t)
(defstub q191693-function-value (function argument) t)
(defstub q191693-set-sequence-value (sequence index) t)
(defstub q191693-measure-sequence-value (sequence index) t)
(defstub q191693-measurable-set-p (measurable set) t)
(defstub q191693-measure-value (measure set) t)
(defstub q191693-lintegral-value
  (lintegral domain measurable measure function) t)

(defun q191693-r-leq (real left right)
  (not (q191693-r-less real right left)))

(defun-sk q191693-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q191693-r-member-p real x)
      (q191693-r-member-p real y)
      (q191693-r-member-p real z))
     (let* ((zero (q191693-r-zero real))
            (one (q191693-r-one real))
            (xy-add (q191693-r-add real x y))
            (yz-add (q191693-r-add real y z))
            (xy-mul (q191693-r-multiply real x y))
            (yz-mul (q191693-r-multiply real y z))
            (neg-x (q191693-r-negate real x))
            (inv-x (q191693-r-inverse real x)))
       (and
        (q191693-r-member-p real xy-add)
        (q191693-r-member-p real xy-mul)
        (q191693-r-member-p real neg-x)
        (q191693-r-member-p real inv-x)
        (equal
         (q191693-r-add real xy-add z)
         (q191693-r-add real x yz-add))
        (equal xy-add (q191693-r-add real y x))
        (equal (q191693-r-add real x zero) x)
        (equal (q191693-r-add real x neg-x) zero)
        (equal
         (q191693-r-multiply real xy-mul z)
         (q191693-r-multiply real x yz-mul))
        (equal xy-mul (q191693-r-multiply real y x))
        (equal (q191693-r-multiply real x one) x)
        (equal (q191693-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q191693-r-multiply real x inv-x)
          one))
        (equal
         (q191693-r-multiply
          real x (q191693-r-add real y z))
         (q191693-r-add
          real
          (q191693-r-multiply real x y)
          (q191693-r-multiply real x z))))))))

(defun-sk q191693-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q191693-r-member-p real x)
      (q191693-r-member-p real y)
      (q191693-r-member-p real z))
     (let ((zero (q191693-r-zero real)))
       (and
        (not (q191693-r-less real x x))
        (or
         (equal x y)
         (q191693-r-less real x y)
         (q191693-r-less real y x))
        (implies
         (and
          (q191693-r-less real x y)
          (q191693-r-less real y z))
         (q191693-r-less real x z))
        (implies
         (q191693-r-less real x y)
         (q191693-r-less
          real
          (q191693-r-add real x z)
          (q191693-r-add real y z)))
        (implies
         (and
          (q191693-r-less real zero x)
          (q191693-r-less real zero y))
         (q191693-r-less
          real zero
          (q191693-r-multiply real x y))))))))

(defun-sk q191693-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q191693-r-member-p real x)
     (q191693-r-set-member-p real set x))))

(defun-sk q191693-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q191693-r-member-p real x)
      (q191693-r-set-member-p real set x))
     (q191693-r-leq real x bound))))

(defun-sk q191693-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q191693-r-member-p real bound)
     (q191693-r-upper-bound-p real set bound))))

(defun-sk q191693-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q191693-r-member-p real supremum)
     (q191693-r-upper-bound-p real set supremum)
     (implies
      (and
       (q191693-r-member-p real bound)
       (q191693-r-upper-bound-p real set bound))
      (q191693-r-leq real supremum bound)))))

(defun-sk q191693-r-has-supremum-p (real set)
  (exists (supremum)
    (q191693-r-supremum-p real set supremum)))

(defun-sk q191693-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q191693-r-set-nonempty-p real set)
      (q191693-r-bounded-above-p real set))
     (q191693-r-has-supremum-p real set))))

(defun q191693-real-field-p (real)
  (let ((zero (q191693-r-zero real))
        (one (q191693-r-one real)))
    (and
     (q191693-r-member-p real zero)
     (q191693-r-member-p real one)
     (not (equal zero one))
     (q191693-r-field-laws-p real)
     (q191693-r-order-laws-p real)
     (q191693-r-less real zero one)
     (q191693-r-dedekind-complete-p real))))

;; Extended nonnegative reals.

(defun q191693-ennreal-p (real value)
  (or
   (equal value :q191693-top)
   (and
    (consp value)
    (equal (car value) :q191693-finite)
    (q191693-r-member-p real (cdr value))
    (q191693-r-leq
     real (q191693-r-zero real) (cdr value)))))

(defun q191693-ennreal-finite (value)
  (cons :q191693-finite value))

(defun q191693-ennreal-zero (real)
  (q191693-ennreal-finite (q191693-r-zero real)))

(defun q191693-ennreal-less (real left right)
  (cond
   ((equal left :q191693-top) nil)
   ((equal right :q191693-top) t)
   (t (q191693-r-less real (cdr left) (cdr right)))))

(defun q191693-ennreal-leq (real left right)
  (not (q191693-ennreal-less real right left)))

(defun q191693-ennreal-add (real left right)
  (if (or (equal left :q191693-top)
          (equal right :q191693-top))
      :q191693-top
    (q191693-ennreal-finite
     (q191693-r-add real (cdr left) (cdr right)))))

(defun q191693-ennreal-multiply (real left right)
  (cond
   ((or (equal left (q191693-ennreal-zero real))
        (equal right (q191693-ennreal-zero real)))
    (q191693-ennreal-zero real))
   ((or (equal left :q191693-top)
        (equal right :q191693-top))
    :q191693-top)
   (t
    (q191693-ennreal-finite
     (q191693-r-multiply real (cdr left) (cdr right))))))

;; Sets, sigma algebras, and countably additive measures.

(defun-sk q191693-valid-set-p (domain set)
  (forall (x)
    (implies
     (q191693-set-member-p set x)
     (q191693-domain-member-p domain x))))

(defun-sk q191693-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q191693-domain-member-p domain x)
     (iff
      (q191693-set-member-p left x)
      (q191693-set-member-p right x)))))

(defun-sk q191693-empty-set-p (domain set)
  (forall (x)
    (iff
     (q191693-set-member-p set x)
     (and (q191693-domain-member-p domain x) nil))))

(defun-sk q191693-complement-set-p (domain set complement)
  (forall (x)
    (iff
     (q191693-set-member-p complement x)
     (and
      (q191693-domain-member-p domain x)
      (not (q191693-set-member-p set x))))))

(defun-sk q191693-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q191693-valid-set-p
      domain
      (q191693-set-sequence-value sequence n)))))

(defun-sk q191693-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q191693-set-member-p
      (q191693-set-sequence-value sequence n)
      x))))

(defun-sk q191693-sequence-union-set-p
    (domain sequence union)
  (forall (x)
    (iff
     (q191693-set-member-p union x)
     (and
      (q191693-domain-member-p domain x)
      (q191693-sequence-union-member-p sequence x)))))

(defun-sk q191693-family-extensional-p (domain measurable)
  (forall (left right)
    (implies
     (q191693-set-equiv-p domain left right)
     (iff
      (q191693-measurable-set-p measurable left)
      (q191693-measurable-set-p measurable right)))))

(defun-sk q191693-family-valid-p (domain measurable)
  (forall (set)
    (implies
     (q191693-measurable-set-p measurable set)
     (q191693-valid-set-p domain set))))

(defun-sk q191693-measurable-empty-exists-p (domain measurable)
  (exists (empty)
    (and
     (q191693-empty-set-p domain empty)
     (q191693-measurable-set-p measurable empty))))

(defun-sk q191693-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q191693-complement-set-p domain set complement)
     (q191693-measurable-set-p measurable complement))))

(defun-sk q191693-measurable-complements-p
    (domain measurable)
  (forall (set)
    (implies
     (q191693-measurable-set-p measurable set)
     (q191693-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q191693-sequence-measurable-p (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q191693-measurable-set-p
      measurable
      (q191693-set-sequence-value sequence n)))))

(defun-sk q191693-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q191693-sequence-union-set-p domain sequence union)
     (q191693-measurable-set-p measurable union))))

(defun-sk q191693-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q191693-set-sequence-p domain sequence)
      (q191693-sequence-measurable-p measurable sequence))
     (q191693-measurable-union-exists-p
      domain measurable sequence))))

(defun q191693-sigma-algebra-p (domain measurable)
  (and
   (q191693-family-extensional-p domain measurable)
   (q191693-family-valid-p domain measurable)
   (q191693-measurable-empty-exists-p domain measurable)
   (q191693-measurable-complements-p domain measurable)
   (q191693-measurable-sequence-unions-p domain measurable)))

(defun-sk q191693-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q191693-set-member-p left x)
      (q191693-set-member-p right x)))))

(defun-sk q191693-pairwise-disjoint-p (sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (q191693-disjoint-sets-p
      (q191693-set-sequence-value sequence m)
      (q191693-set-sequence-value sequence n)))))

(defun q191693-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q191693-ennreal-zero real)
    (q191693-ennreal-add
     real
     (q191693-measure-prefix-sum
      real measure sequence (1- count))
     (q191693-measure-value
      measure
      (q191693-set-sequence-value sequence (1- count))))))

(defun-sk q191693-countable-sum-upper-bound-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q191693-ennreal-leq
      real
      (q191693-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q191693-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q191693-ennreal-p real total)
     (q191693-countable-sum-upper-bound-p
      real measure sequence total)
     (implies
      (and
       (q191693-ennreal-p real bound)
       (q191693-countable-sum-upper-bound-p
        real measure sequence bound))
      (q191693-ennreal-leq real total bound)))))

(defun-sk q191693-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q191693-set-equiv-p domain left right)
     (equal
      (q191693-measure-value measure left)
      (q191693-measure-value measure right)))))

(defun-sk q191693-measure-values-p
    (real domain measurable measure)
  (forall (set)
    (implies
     (and
      (q191693-valid-set-p domain set)
      (q191693-measurable-set-p measurable set))
     (q191693-ennreal-p
      real (q191693-measure-value measure set)))))

(defun-sk q191693-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q191693-empty-set-p domain empty)
     (equal
      (q191693-measure-value measure empty)
      (q191693-ennreal-zero real)))))

(defun-sk q191693-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q191693-set-sequence-p domain sequence)
      (q191693-sequence-measurable-p measurable sequence)
      (q191693-pairwise-disjoint-p sequence)
      (q191693-sequence-union-set-p domain sequence union))
     (q191693-countable-sum-p
      real measure sequence
      (q191693-measure-value measure union)))))

(defun q191693-measure-space-p
    (real domain measurable measure)
  (and
   (q191693-sigma-algebra-p domain measurable)
   (q191693-measure-extensional-p domain measure)
   (q191693-measure-values-p real domain measurable measure)
   (q191693-measure-empty-zero-p real domain measure)
   (q191693-countably-additive-p
    real domain measurable measure)))

;; Finite, s-finite, and sigma-finite measures.

(defun-sk q191693-universe-set-p (domain set)
  (forall (x)
    (iff
     (q191693-set-member-p set x)
     (q191693-domain-member-p domain x))))

(defun-sk q191693-finite-measure-p
    (real domain measurable measure)
  (exists (universe)
    (and
     (q191693-universe-set-p domain universe)
     (q191693-measurable-set-p measurable universe)
     (q191693-ennreal-less
      real
      (q191693-measure-value measure universe)
      :q191693-top))))

(defun-sk q191693-finite-measure-sequence-p
    (real domain measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((measure
            (q191693-measure-sequence-value sequence n)))
       (and
        (q191693-measure-space-p
         real domain measurable measure)
        (q191693-finite-measure-p
         real domain measurable measure))))))

(defun q191693-measure-sequence-prefix-sum
    (real sequence set count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q191693-ennreal-zero real)
    (q191693-ennreal-add
     real
     (q191693-measure-sequence-prefix-sum
      real sequence set (1- count))
     (q191693-measure-value
      (q191693-measure-sequence-value sequence (1- count))
      set))))

(defun-sk q191693-measure-sequence-sum-upper-bound-p
    (real sequence set bound)
  (forall (count)
    (implies
     (natp count)
     (q191693-ennreal-leq
      real
      (q191693-measure-sequence-prefix-sum
       real sequence set count)
      bound))))

(defun-sk q191693-measure-sequence-sum-value-p
    (real sequence set total)
  (forall (bound)
    (and
     (q191693-ennreal-p real total)
     (q191693-measure-sequence-sum-upper-bound-p
      real sequence set total)
     (implies
      (and
       (q191693-ennreal-p real bound)
       (q191693-measure-sequence-sum-upper-bound-p
        real sequence set bound))
      (q191693-ennreal-leq real total bound)))))

(defun-sk q191693-measure-is-sequence-sum-p
    (real measurable sequence measure)
  (forall (set)
    (implies
     (q191693-measurable-set-p measurable set)
     (q191693-measure-sequence-sum-value-p
      real sequence set
      (q191693-measure-value measure set)))))

(defun-sk q191693-s-finite-measure-p
    (real domain measurable measure)
  (exists (sequence)
    (and
     (q191693-finite-measure-sequence-p
      real domain measurable sequence)
     (q191693-measure-is-sequence-sum-p
      real measurable sequence measure))))

(defun-sk q191693-sequence-covers-domain-p
    (domain sequence)
  (forall (x)
    (implies
     (q191693-domain-member-p domain x)
     (q191693-sequence-union-member-p sequence x))))

(defun-sk q191693-sequence-has-finite-measure-p
    (real measurable measure sequence)
  (forall (n)
    (implies
     (natp n)
     (and
      (q191693-measurable-set-p
       measurable
       (q191693-set-sequence-value sequence n))
      (q191693-ennreal-less
       real
       (q191693-measure-value
        measure
        (q191693-set-sequence-value sequence n))
       :q191693-top)))))

(defun-sk q191693-sigma-finite-measure-p
    (real domain measurable measure)
  (exists (sequence)
    (and
     (q191693-set-sequence-p domain sequence)
     (q191693-sequence-covers-domain-p domain sequence)
     (q191693-sequence-has-finite-measure-p
      real measurable measure sequence))))

;; Measurable extended-nonnegative-real functions.

(defun-sk q191693-ennreal-function-p (real domain function)
  (forall (x)
    (implies
     (q191693-domain-member-p domain x)
     (q191693-ennreal-p
      real (q191693-function-value function x)))))

(defun-sk q191693-ennreal-upper-preimage-set-p
    (real domain function threshold set)
  (forall (x)
    (iff
     (q191693-set-member-p set x)
     (and
      (q191693-domain-member-p domain x)
      (q191693-ennreal-less
       real threshold
       (q191693-function-value function x))))))

(defun-sk q191693-ennreal-upper-preimage-exists-p
    (real domain measurable function threshold)
  (exists (set)
    (and
     (q191693-ennreal-upper-preimage-set-p
      real domain function threshold set)
     (q191693-measurable-set-p measurable set))))

(defun-sk q191693-measurable-ennreal-function-p
    (real domain measurable function)
  (forall (threshold)
    (and
     (q191693-ennreal-function-p real domain function)
     (implies
      (q191693-ennreal-p real threshold)
      (q191693-ennreal-upper-preimage-exists-p
       real domain measurable function threshold)))))

;; The lower Lebesgue integral is the supremum of integrals of measurable
;; finite-range simple functions below the integrand.

(defun-sk q191693-value-attained-p
    (domain function value)
  (exists (x)
    (and
     (q191693-domain-member-p domain x)
     (equal
      (q191693-function-value function x)
      value))))

(defun q191693-values-attained-p
    (domain function values)
  (if (consp values)
      (and
       (q191693-value-attained-p
        domain function (car values))
       (q191693-values-attained-p
        domain function (cdr values)))
    (equal values nil)))

(defun q191693-ennreal-value-list-p (real values)
  (if (consp values)
      (and
       (q191693-ennreal-p real (car values))
       (q191693-ennreal-value-list-p real (cdr values)))
    (equal values nil)))

(defun-sk q191693-range-in-values-p
    (domain function values)
  (forall (x)
    (implies
     (q191693-domain-member-p domain x)
     (member-equal
      (q191693-function-value function x)
      values))))

(defun-sk q191693-fiber-set-p
    (domain function value set)
  (forall (x)
    (iff
     (q191693-set-member-p set x)
     (and
      (q191693-domain-member-p domain x)
      (equal
       (q191693-function-value function x)
       value)))))

(defun q191693-fiber-list-p
    (domain function values fibers)
  (if (consp values)
      (and
       (consp fibers)
       (q191693-fiber-set-p
        domain function (car values) (car fibers))
       (q191693-fiber-list-p
        domain function (cdr values) (cdr fibers)))
    (equal fibers nil)))

(defun q191693-finite-simple-integral
    (real measure values fibers)
  (if (consp values)
      (q191693-ennreal-add
       real
       (q191693-ennreal-multiply
        real
        (car values)
        (q191693-measure-value measure (car fibers)))
       (q191693-finite-simple-integral
        real measure (cdr values) (cdr fibers)))
    (q191693-ennreal-zero real)))

(defun q191693-simple-function-data-p
    (real domain measurable function values fibers)
  (and
   (true-listp values)
   (true-listp fibers)
   (no-duplicatesp-equal values)
   (q191693-ennreal-value-list-p real values)
   (q191693-values-attained-p domain function values)
   (q191693-range-in-values-p domain function values)
   (q191693-fiber-list-p domain function values fibers)
   (q191693-measurable-ennreal-function-p
    real domain measurable function)))

(defun-sk q191693-simple-below-p
    (real domain simple function)
  (forall (x)
    (implies
     (q191693-domain-member-p domain x)
     (q191693-ennreal-leq
      real
      (q191693-function-value simple x)
      (q191693-function-value function x)))))

(defun-sk q191693-lintegral-upper-bound-p
    (real domain measurable measure function bound)
  (forall (simple values fibers)
    (implies
     (and
      (q191693-simple-function-data-p
       real domain measurable simple values fibers)
      (q191693-simple-below-p
       real domain simple function))
     (q191693-ennreal-leq
      real
      (q191693-finite-simple-integral
       real measure values fibers)
      bound))))

(defun-sk q191693-lintegral-value-p
    (real domain measurable measure function value)
  (forall (bound)
    (and
     (q191693-ennreal-function-p real domain function)
     (q191693-ennreal-p real value)
     (q191693-lintegral-upper-bound-p
      real domain measurable measure function value)
     (implies
      (and
       (q191693-ennreal-p real bound)
       (q191693-lintegral-upper-bound-p
        real domain measurable measure function bound))
      (q191693-ennreal-leq real value bound)))))

(defun-sk q191693-lintegral-operation-p
    (real domain measurable lintegral)
  (forall (measure function)
    (implies
     (and
      (q191693-measure-space-p
       real domain measurable measure)
      (q191693-ennreal-function-p real domain function))
     (q191693-lintegral-value-p
      real domain measurable measure function
      (q191693-lintegral-value
       lintegral domain measurable measure function)))))

;; Measure equality, addition, absolute continuity, and mutual singularity.

(defun-sk q191693-measure-equal-p
    (domain measurable left right)
  (forall (set)
    (implies
     (q191693-measurable-set-p measurable set)
     (equal
      (q191693-measure-value left set)
      (q191693-measure-value right set)))))

(defun-sk q191693-measure-addition-p
    (real measurable left right total)
  (forall (set)
    (implies
     (q191693-measurable-set-p measurable set)
     (equal
      (q191693-measure-value total set)
      (q191693-ennreal-add
       real
       (q191693-measure-value left set)
       (q191693-measure-value right set))))))

(defun-sk q191693-absolutely-continuous-p
    (real measurable mu nu)
  (forall (set)
    (implies
     (and
      (q191693-measurable-set-p measurable set)
      (equal
       (q191693-measure-value nu set)
       (q191693-ennreal-zero real)))
     (equal
      (q191693-measure-value mu set)
      (q191693-ennreal-zero real)))))

(defun-sk q191693-mutually-singular-p
    (real domain measurable left right)
  (exists (set complement)
    (and
     (q191693-measurable-set-p measurable set)
     (q191693-complement-set-p domain set complement)
     (q191693-measurable-set-p measurable complement)
     (equal
      (q191693-measure-value left set)
      (q191693-ennreal-zero real))
     (equal
      (q191693-measure-value right complement)
      (q191693-ennreal-zero real)))))

;; The measure with density f has value integral (1_s f) dnu on each
;; measurable set s.

(defun-sk q191693-restricted-density-function-p
    (real domain set density restricted)
  (forall (x)
    (and
     (q191693-ennreal-function-p real domain restricted)
     (implies
      (q191693-domain-member-p domain x)
      (equal
       (q191693-function-value restricted x)
       (if (q191693-set-member-p set x)
           (q191693-function-value density x)
         (q191693-ennreal-zero real)))))))

(defun-sk q191693-with-density-value-p
    (real domain measurable base density lintegral set value)
  (exists (restricted)
    (and
     (q191693-restricted-density-function-p
      real domain set density restricted)
     (equal
      value
      (q191693-lintegral-value
       lintegral domain measurable base restricted)))))

(defun-sk q191693-with-density-values-p
    (real domain measurable base density density-measure lintegral)
  (forall (set)
    (implies
     (q191693-measurable-set-p measurable set)
     (q191693-with-density-value-p
      real domain measurable base density lintegral set
      (q191693-measure-value density-measure set)))))

(defun q191693-with-density-p
    (real domain measurable base density density-measure lintegral)
  (and
   (q191693-measure-space-p
    real domain measurable density-measure)
   (q191693-measurable-ennreal-function-p
    real domain measurable density)
   (q191693-with-density-values-p
    real domain measurable base density density-measure lintegral)))

;; HaveLebesgueDecomposition is the source existential package.

(defun q191693-decomposition-singular-part (package)
  (nth 0 package))

(defun q191693-decomposition-derivative (package)
  (nth 1 package))

(defun q191693-decomposition-density-measure (package)
  (nth 2 package))

(defun q191693-decomposition-package-p
    (real domain measurable mu nu lintegral package)
  (let ((singular-part
         (q191693-decomposition-singular-part package))
        (derivative
         (q191693-decomposition-derivative package))
        (density-measure
         (q191693-decomposition-density-measure package)))
    (and
     (true-listp package)
     (equal (len package) 3)
     (q191693-measure-space-p
      real domain measurable singular-part)
     (q191693-with-density-p
      real domain measurable nu derivative density-measure lintegral)
     (q191693-mutually-singular-p
      real domain measurable singular-part nu)
     (q191693-measure-addition-p
      real measurable singular-part density-measure mu))))

(defun-sk q191693-have-lebesgue-decomposition-p
    (real domain measurable mu nu lintegral)
  (exists (package)
    (q191693-decomposition-package-p
     real domain measurable mu nu lintegral package)))

(defun-sk thousand-theorems-q191693-lebesgue-decomposition-statement ()
  (forall (real domain measurable mu nu lintegral)
    (implies
     (and
      (q191693-real-field-p real)
      (q191693-measure-space-p
       real domain measurable mu)
      (q191693-measure-space-p
       real domain measurable nu)
      (q191693-lintegral-operation-p
       real domain measurable lintegral)
      (q191693-s-finite-measure-p
       real domain measurable mu)
      (q191693-sigma-finite-measure-p
       real domain measurable nu))
     (q191693-have-lebesgue-decomposition-p
      real domain measurable mu nu lintegral))))

(value-triple :itpeval-statement-checked)
:q
