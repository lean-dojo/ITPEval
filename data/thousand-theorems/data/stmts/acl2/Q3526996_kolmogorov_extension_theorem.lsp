;; Statement-only formalization of thousand-theorems corpus artifact Q3526996,
;; "Kolmogorov extension theorem": a projectively consistent family of finite
;; measures on all finite products of arbitrary Polish Borel coordinate spaces
;; extends to a measure on the unrestricted dependent product with exactly
;; those finite-dimensional marginals. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Carriers, sets, functions, topologies, sigma algebras, and measures are
;; unrestricted ACL2 objects.  The quantified predicates below impose the real
;; field, metric, Polish, Borel, dependent-product, and countable-additivity
;; laws explicitly.  Finite coordinate sets are represented by finite lists,
;; but neither the index carrier nor any coordinate carrier is made finite.

(defstub q3526996-domain-member-p (domain object) t)
(defstub q3526996-set-member-p (set object) t)
(defstub q3526996-family-member-p (family set) t)
(defstub q3526996-function-at (function argument) t)
(defstub q3526996-sequence-at (sequence index) t)
(defstub q3526996-open-set-p (topology set) t)
(defstub q3526996-measurable-set-p (sigma set) t)

(defstub q3526996-r-member-p (real value) t)
(defstub q3526996-r-zero (real) t)
(defstub q3526996-r-one (real) t)
(defstub q3526996-r-add (real left right) t)
(defstub q3526996-r-multiply (real left right) t)
(defstub q3526996-r-negate (real value) t)
(defstub q3526996-r-inverse (real value) t)
(defstub q3526996-r-less (real left right) t)
(defstub q3526996-r-set-member-p (real set value) t)

(defstub q3526996-empty-set (domain) t)
(defstub q3526996-full-set (domain) t)
(defstub q3526996-complement-set (domain set) t)
(defstub q3526996-intersection-set (domain left right) t)
(defstub q3526996-countable-union-set (domain sequence) t)
(defstub q3526996-arbitrary-union-set (domain family) t)

(defstub q3526996-measure-value (measure set) t)

(defstub q3526996-state-domain (spaces index) t)
(defstub q3526996-state-topology (spaces index) t)
(defstub q3526996-state-sigma (spaces index) t)
(defstub q3526996-metric-distance (metric left right) t)
(defstub q3526996-open-ball (real domain metric center radius) t)

(defstub q3526996-finite-product-domain (spaces index-set) t)
(defstub q3526996-finite-product-sigma (spaces index-set) t)
(defstub q3526996-full-product-domain (spaces index-domain) t)
(defstub q3526996-full-product-sigma (spaces index-domain) t)
(defstub q3526996-finite-coordinate
  (spaces index-set tuple index) t)
(defstub q3526996-full-coordinate
  (spaces index-domain tuple index) t)
(defstub q3526996-finite-restrict
  (spaces larger-set smaller-set tuple) t)
(defstub q3526996-full-restrict
  (spaces index-domain index-set tuple) t)
(defstub q3526996-finite-coordinate-cylinder
  (spaces index-set index state-set) t)
(defstub q3526996-full-coordinate-cylinder
  (spaces index-domain index state-set) t)
(defstub q3526996-finite-restriction-preimage
  (spaces larger-set smaller-set set) t)
(defstub q3526996-full-restriction-preimage
  (spaces index-domain index-set set) t)

(defstub q3526996-family-measure (measure-family index-set) t)

;; A Dedekind-complete ordered field presents the real numbers used for both
;; metric distances and the finite values of the source's finite measures.

(defun q3526996-r-leq (real left right)
  (not (q3526996-r-less real right left)))

(defun q3526996-r-positive-p (real value)
  (and
   (q3526996-r-member-p real value)
   (q3526996-r-less
    real (q3526996-r-zero real) value)))

(defun q3526996-r-nonnegative-p (real value)
  (and
   (q3526996-r-member-p real value)
   (q3526996-r-leq
    real (q3526996-r-zero real) value)))

(defun-sk q3526996-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3526996-r-member-p real x)
      (q3526996-r-member-p real y)
      (q3526996-r-member-p real z))
     (let* ((zero (q3526996-r-zero real))
            (one (q3526996-r-one real))
            (xy-add (q3526996-r-add real x y))
            (yz-add (q3526996-r-add real y z))
            (xy-mul (q3526996-r-multiply real x y))
            (yz-mul (q3526996-r-multiply real y z))
            (neg-x (q3526996-r-negate real x))
            (inv-x (q3526996-r-inverse real x)))
       (and
        (q3526996-r-member-p real xy-add)
        (q3526996-r-member-p real xy-mul)
        (q3526996-r-member-p real neg-x)
        (q3526996-r-member-p real inv-x)
        (equal
         (q3526996-r-add real xy-add z)
         (q3526996-r-add real x yz-add))
        (equal xy-add (q3526996-r-add real y x))
        (equal (q3526996-r-add real x zero) x)
        (equal (q3526996-r-add real x neg-x) zero)
        (equal
         (q3526996-r-multiply real xy-mul z)
         (q3526996-r-multiply real x yz-mul))
        (equal xy-mul (q3526996-r-multiply real y x))
        (equal (q3526996-r-multiply real x one) x)
        (equal (q3526996-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q3526996-r-multiply real x inv-x)
          one))
        (equal
         (q3526996-r-multiply
          real x (q3526996-r-add real y z))
         (q3526996-r-add
          real
          (q3526996-r-multiply real x y)
          (q3526996-r-multiply real x z))))))))

(defun-sk q3526996-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3526996-r-member-p real x)
      (q3526996-r-member-p real y)
      (q3526996-r-member-p real z))
     (let ((zero (q3526996-r-zero real)))
       (and
        (not (q3526996-r-less real x x))
        (or
         (equal x y)
         (q3526996-r-less real x y)
         (q3526996-r-less real y x))
        (implies
         (and
          (q3526996-r-less real x y)
          (q3526996-r-less real y z))
         (q3526996-r-less real x z))
        (implies
         (q3526996-r-less real x y)
         (q3526996-r-less
          real
          (q3526996-r-add real x z)
          (q3526996-r-add real y z)))
        (implies
         (and
          (q3526996-r-less real zero x)
          (q3526996-r-less real zero y))
         (q3526996-r-less
          real zero
          (q3526996-r-multiply real x y))))))))

(defun-sk q3526996-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q3526996-r-member-p real x)
     (q3526996-r-set-member-p real set x))))

(defun-sk q3526996-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q3526996-r-member-p real x)
      (q3526996-r-set-member-p real set x))
     (q3526996-r-leq real x bound))))

(defun-sk q3526996-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q3526996-r-member-p real bound)
     (q3526996-r-upper-bound-p real set bound))))

(defun-sk q3526996-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q3526996-r-member-p real supremum)
     (q3526996-r-upper-bound-p real set supremum)
     (implies
      (and
       (q3526996-r-member-p real bound)
       (q3526996-r-upper-bound-p real set bound))
      (q3526996-r-leq real supremum bound)))))

(defun-sk q3526996-r-supremum-exists-p (real set)
  (exists (supremum)
    (q3526996-r-supremum-p real set supremum)))

(defun-sk q3526996-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q3526996-r-set-nonempty-p real set)
      (q3526996-r-bounded-above-p real set))
     (q3526996-r-supremum-exists-p real set))))

(defun q3526996-real-field-p (real)
  (let ((zero (q3526996-r-zero real))
        (one (q3526996-r-one real)))
    (and
     (q3526996-r-member-p real zero)
     (q3526996-r-member-p real one)
     (not (equal zero one))
     (q3526996-r-field-laws-p real)
     (q3526996-r-order-laws-p real)
     (q3526996-r-less real zero one)
     (q3526996-r-dedekind-complete-p real))))

;; Arbitrary sets, topologies, and sigma algebras.

(defun-sk q3526996-valid-set-p (domain set)
  (forall (x)
    (implies
     (q3526996-set-member-p set x)
     (q3526996-domain-member-p domain x))))

(defun-sk q3526996-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q3526996-domain-member-p domain x)
     (iff
      (q3526996-set-member-p left x)
      (q3526996-set-member-p right x)))))

(defun-sk q3526996-set-subset-p (domain left right)
  (forall (x)
    (implies
     (and
      (q3526996-domain-member-p domain x)
      (q3526996-set-member-p left x))
     (q3526996-set-member-p right x))))

(defun-sk q3526996-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q3526996-valid-set-p
      domain (q3526996-sequence-at sequence n)))))

(defun-sk q3526996-measurable-sequence-p (sigma sequence)
  (forall (n)
    (implies
     (natp n)
     (q3526996-measurable-set-p
      sigma (q3526996-sequence-at sequence n)))))

(defun-sk q3526996-pairwise-disjoint-p (sequence)
  (forall (m n x)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (not
      (and
       (q3526996-set-member-p
        (q3526996-sequence-at sequence m) x)
       (q3526996-set-member-p
        (q3526996-sequence-at sequence n) x))))))

(defun-sk q3526996-sequence-union-member-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q3526996-set-member-p
      (q3526996-sequence-at sequence n) x))))

(defun-sk q3526996-family-valid-p (domain family)
  (forall (set)
    (implies
     (q3526996-family-member-p family set)
     (q3526996-valid-set-p domain set))))

(defun-sk q3526996-family-union-member-p (family x)
  (exists (set)
    (and
     (q3526996-family-member-p family set)
     (q3526996-set-member-p set x))))

(defun-sk q3526996-basic-set-constructor-laws-p (domain)
  (forall (left right sequence family x)
    (and
     (iff
      (q3526996-set-member-p
       (q3526996-empty-set domain) x)
      nil)
     (iff
      (q3526996-set-member-p
       (q3526996-full-set domain) x)
      (q3526996-domain-member-p domain x))
     (implies
      (q3526996-valid-set-p domain left)
      (iff
       (q3526996-set-member-p
        (q3526996-complement-set domain left) x)
       (and
        (q3526996-domain-member-p domain x)
        (not (q3526996-set-member-p left x)))))
     (implies
      (and
       (q3526996-valid-set-p domain left)
       (q3526996-valid-set-p domain right))
      (iff
       (q3526996-set-member-p
        (q3526996-intersection-set domain left right) x)
       (and
        (q3526996-domain-member-p domain x)
        (q3526996-set-member-p left x)
        (q3526996-set-member-p right x))))
     (implies
      (q3526996-set-sequence-p domain sequence)
      (iff
       (q3526996-set-member-p
        (q3526996-countable-union-set domain sequence) x)
       (and
        (q3526996-domain-member-p domain x)
        (q3526996-sequence-union-member-p sequence x))))
     (implies
      (q3526996-family-valid-p domain family)
      (iff
       (q3526996-set-member-p
        (q3526996-arbitrary-union-set domain family) x)
       (and
        (q3526996-domain-member-p domain x)
        (q3526996-family-union-member-p family x)))))))

(defun-sk q3526996-topology-extensional-p (domain topology)
  (forall (left right)
    (implies
     (q3526996-set-equiv-p domain left right)
     (iff
      (q3526996-open-set-p topology left)
      (q3526996-open-set-p topology right)))))

(defun-sk q3526996-topology-members-valid-p (domain topology)
  (forall (set)
    (implies
     (q3526996-open-set-p topology set)
     (q3526996-valid-set-p domain set))))

(defun-sk q3526996-open-intersections-p (domain topology)
  (forall (left right)
    (implies
     (and
      (q3526996-open-set-p topology left)
      (q3526996-open-set-p topology right))
     (q3526996-open-set-p
      topology
      (q3526996-intersection-set domain left right)))))

(defun-sk q3526996-open-family-p (topology family)
  (forall (set)
    (implies
     (q3526996-family-member-p family set)
     (q3526996-open-set-p topology set))))

(defun-sk q3526996-open-arbitrary-unions-p (domain topology)
  (forall (family)
    (implies
     (and
      (q3526996-family-valid-p domain family)
      (q3526996-open-family-p topology family))
     (q3526996-open-set-p
      topology
      (q3526996-arbitrary-union-set domain family)))))

(defun q3526996-topological-space-p (domain topology)
  (and
   (q3526996-basic-set-constructor-laws-p domain)
   (q3526996-topology-extensional-p domain topology)
   (q3526996-topology-members-valid-p domain topology)
   (q3526996-open-set-p
    topology (q3526996-empty-set domain))
   (q3526996-open-set-p
    topology (q3526996-full-set domain))
   (q3526996-open-intersections-p domain topology)
   (q3526996-open-arbitrary-unions-p domain topology)))

(defun-sk q3526996-sigma-extensional-p (domain sigma)
  (forall (left right)
    (implies
     (q3526996-set-equiv-p domain left right)
     (iff
      (q3526996-measurable-set-p sigma left)
      (q3526996-measurable-set-p sigma right)))))

(defun-sk q3526996-sigma-members-valid-p (domain sigma)
  (forall (set)
    (implies
     (q3526996-measurable-set-p sigma set)
     (q3526996-valid-set-p domain set))))

(defun-sk q3526996-sigma-complements-p (domain sigma)
  (forall (set)
    (implies
     (q3526996-measurable-set-p sigma set)
     (q3526996-measurable-set-p
      sigma (q3526996-complement-set domain set)))))

(defun-sk q3526996-sigma-countable-unions-p (domain sigma)
  (forall (sequence)
    (implies
     (and
      (q3526996-set-sequence-p domain sequence)
      (q3526996-measurable-sequence-p sigma sequence))
     (q3526996-measurable-set-p
      sigma
      (q3526996-countable-union-set domain sequence)))))

(defun q3526996-sigma-algebra-p (domain sigma)
  (and
   (q3526996-basic-set-constructor-laws-p domain)
   (q3526996-sigma-extensional-p domain sigma)
   (q3526996-sigma-members-valid-p domain sigma)
   (q3526996-measurable-set-p
    sigma (q3526996-empty-set domain))
   (q3526996-sigma-complements-p domain sigma)
   (q3526996-sigma-countable-unions-p domain sigma)))

;; Finite, countably additive measures.  Since every value lies in the real
;; carrier, this is the finite-measure specialization of ENNReal-valued measure.

(defun q3526996-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q3526996-r-zero real)
    (q3526996-r-add
     real
     (q3526996-measure-prefix-sum
      real measure sequence (- count 1))
     (q3526996-measure-value
      measure
      (q3526996-sequence-at sequence (- count 1))))))

(defun-sk q3526996-measure-prefix-sums-bounded-p
    (real measure sequence bound)
  (forall (count)
    (implies
     (natp count)
     (q3526996-r-leq
      real
      (q3526996-measure-prefix-sum
       real measure sequence count)
      bound))))

(defun-sk q3526996-measure-countable-sum-p
    (real measure sequence total)
  (forall (bound)
    (and
     (q3526996-r-member-p real total)
     (q3526996-measure-prefix-sums-bounded-p
      real measure sequence total)
     (implies
      (and
       (q3526996-r-member-p real bound)
       (q3526996-measure-prefix-sums-bounded-p
        real measure sequence bound))
      (q3526996-r-leq real total bound)))))

(defun-sk q3526996-measure-extensional-p (domain measure)
  (forall (left right)
    (implies
     (q3526996-set-equiv-p domain left right)
     (equal
      (q3526996-measure-value measure left)
      (q3526996-measure-value measure right)))))

(defun-sk q3526996-measure-values-p (real sigma measure)
  (forall (set)
    (implies
     (q3526996-measurable-set-p sigma set)
     (q3526996-r-nonnegative-p
      real (q3526996-measure-value measure set)))))

(defun-sk q3526996-countably-additive-p
    (real domain sigma measure)
  (forall (sequence)
    (implies
     (and
      (q3526996-set-sequence-p domain sequence)
      (q3526996-measurable-sequence-p sigma sequence)
      (q3526996-pairwise-disjoint-p sequence))
     (q3526996-measure-countable-sum-p
      real measure sequence
      (q3526996-measure-value
       measure
       (q3526996-countable-union-set domain sequence))))))

(defun q3526996-finite-measure-p
    (real domain sigma measure)
  (and
   (q3526996-sigma-algebra-p domain sigma)
   (q3526996-measure-extensional-p domain measure)
   (q3526996-measure-values-p real sigma measure)
   (equal
    (q3526996-measure-value
     measure (q3526996-empty-set domain))
    (q3526996-r-zero real))
   (q3526996-countably-additive-p
    real domain sigma measure)))

;; Polish spaces and their Borel sigma algebras.

(defun-sk q3526996-metric-laws-p (real domain metric)
  (forall (x y z)
    (implies
     (and
      (q3526996-domain-member-p domain x)
      (q3526996-domain-member-p domain y)
      (q3526996-domain-member-p domain z))
     (let ((dxy (q3526996-metric-distance metric x y))
           (dyx (q3526996-metric-distance metric y x))
           (dxz (q3526996-metric-distance metric x z))
           (dyz (q3526996-metric-distance metric y z)))
       (and
        (q3526996-r-nonnegative-p real dxy)
        (q3526996-r-nonnegative-p real dyx)
        (q3526996-r-nonnegative-p real dxz)
        (q3526996-r-nonnegative-p real dyz)
        (iff
         (equal dxy (q3526996-r-zero real))
         (equal x y))
        (equal dxy dyx)
        (q3526996-r-leq
         real dxz
         (q3526996-r-add real dxy dyz)))))))

(defun-sk q3526996-open-ball-laws-p
    (real domain metric)
  (forall (center radius x)
    (implies
     (and
      (q3526996-domain-member-p domain center)
      (q3526996-r-positive-p real radius))
     (iff
      (q3526996-set-member-p
       (q3526996-open-ball
        real domain metric center radius)
       x)
      (and
       (q3526996-domain-member-p domain x)
       (q3526996-r-less
        real
        (q3526996-metric-distance metric center x)
        radius))))))

(defun-sk q3526996-ball-contained-p
    (real domain metric set center radius)
  (forall (x)
    (implies
     (q3526996-set-member-p
      (q3526996-open-ball
       real domain metric center radius)
      x)
     (q3526996-set-member-p set x))))

(defun-sk q3526996-open-radius-exists-p
    (real domain metric set center)
  (exists (radius)
    (and
     (q3526996-r-positive-p real radius)
     (q3526996-ball-contained-p
      real domain metric set center radius))))

(defun-sk q3526996-metric-open-p
    (real domain metric set)
  (forall (center)
    (implies
     (and
      (q3526996-domain-member-p domain center)
      (q3526996-set-member-p set center))
     (q3526996-open-radius-exists-p
      real domain metric set center))))

(defun-sk q3526996-metric-topology-p
    (real domain topology metric)
  (forall (set)
    (implies
     (q3526996-valid-set-p domain set)
     (iff
      (q3526996-open-set-p topology set)
      (q3526996-metric-open-p
       real domain metric set)))))

(defun-sk q3526996-domain-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q3526996-domain-member-p
      domain (q3526996-sequence-at sequence n)))))

(defun-sk q3526996-cauchy-tail-p
    (real domain metric sequence radius cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (<= cutoff m)
      (<= cutoff n))
     (q3526996-r-less
      real
      (q3526996-metric-distance
       metric
       (q3526996-sequence-at sequence m)
       (q3526996-sequence-at sequence n))
      radius))))

(defun-sk q3526996-cauchy-cutoff-exists-p
    (real domain metric sequence radius)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q3526996-cauchy-tail-p
      real domain metric sequence radius cutoff))))

(defun-sk q3526996-cauchy-sequence-p
    (real domain metric sequence)
  (forall (radius)
    (and
     (q3526996-domain-sequence-p domain sequence)
     (implies
      (q3526996-r-positive-p real radius)
      (q3526996-cauchy-cutoff-exists-p
       real domain metric sequence radius)))))

(defun-sk q3526996-convergence-tail-p
    (real domain metric sequence limit radius cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (q3526996-r-less
      real
      (q3526996-metric-distance
       metric (q3526996-sequence-at sequence n) limit)
      radius))))

(defun-sk q3526996-convergence-cutoff-exists-p
    (real domain metric sequence limit radius)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q3526996-convergence-tail-p
      real domain metric sequence limit radius cutoff))))

(defun-sk q3526996-sequence-converges-p
    (real domain metric sequence limit)
  (forall (radius)
    (and
     (q3526996-domain-member-p domain limit)
     (implies
      (q3526996-r-positive-p real radius)
      (q3526996-convergence-cutoff-exists-p
       real domain metric sequence limit radius)))))

(defun-sk q3526996-sequence-limit-exists-p
    (real domain metric sequence)
  (exists (limit)
    (q3526996-sequence-converges-p
     real domain metric sequence limit)))

(defun-sk q3526996-complete-metric-p
    (real domain metric)
  (forall (sequence)
    (implies
     (q3526996-cauchy-sequence-p
      real domain metric sequence)
     (q3526996-sequence-limit-exists-p
      real domain metric sequence))))

(defun-sk q3526996-enumerator-index-exists-p
    (enumerator x)
  (exists (n)
    (and
     (natp n)
     (equal
      (q3526996-function-at enumerator n)
      x))))

(defun-sk q3526996-enumerator-hits-set-p
    (set enumerator)
  (forall (x)
    (implies
     (q3526996-set-member-p set x)
     (q3526996-enumerator-index-exists-p
      enumerator
      x))))

(defun-sk q3526996-dense-point-exists-p
    (real domain metric set x radius)
  (exists (y)
    (and
     (q3526996-set-member-p set y)
     (q3526996-domain-member-p domain y)
     (q3526996-r-less
      real
      (q3526996-metric-distance metric x y)
      radius))))

(defun-sk q3526996-dense-set-p
    (real domain metric set)
  (forall (x radius)
    (implies
     (and
      (q3526996-domain-member-p domain x)
      (q3526996-r-positive-p real radius))
     (q3526996-dense-point-exists-p
      real
      domain
      metric
      set
      x
      radius))))

(defun q3526996-polish-witness-p
    (real domain topology metric dense-set enumerator)
  (and
   (q3526996-metric-laws-p real domain metric)
   (q3526996-open-ball-laws-p real domain metric)
   (q3526996-metric-topology-p
    real domain topology metric)
   (q3526996-complete-metric-p real domain metric)
   (q3526996-valid-set-p domain dense-set)
   (q3526996-enumerator-hits-set-p dense-set enumerator)
   (q3526996-dense-set-p
    real domain metric dense-set)))

(defun-sk q3526996-polish-space-p
    (real domain topology)
  (exists (metric dense-set enumerator)
    (q3526996-polish-witness-p
     real domain topology metric dense-set enumerator)))

(defun-sk q3526996-opens-measurable-p (topology sigma)
  (forall (set)
    (implies
     (q3526996-open-set-p topology set)
     (q3526996-measurable-set-p sigma set))))

(defun-sk q3526996-borel-minimal-p
    (domain topology sigma)
  (forall (candidate set)
    (implies
     (and
      (q3526996-sigma-algebra-p domain candidate)
      (q3526996-opens-measurable-p topology candidate)
      (q3526996-measurable-set-p sigma set))
     (q3526996-measurable-set-p candidate set))))

(defun q3526996-polish-borel-space-p
    (real domain topology sigma)
  (and
   (q3526996-topological-space-p domain topology)
   (q3526996-polish-space-p real domain topology)
   (q3526996-sigma-algebra-p domain sigma)
   (q3526996-opens-measurable-p topology sigma)
   (q3526996-borel-minimal-p domain topology sigma)))

(defun-sk q3526996-coordinate-space-family-p
    (real index-domain spaces)
  (forall (index)
    (implies
     (q3526996-domain-member-p index-domain index)
     (q3526996-polish-borel-space-p
      real
      (q3526996-state-domain spaces index)
      (q3526996-state-topology spaces index)
      (q3526996-state-sigma spaces index)))))

;; Arbitrary finite index sets and dependent products.

(defun q3526996-list-in-domain-p (domain values)
  (if (consp values)
      (and
       (q3526996-domain-member-p domain (car values))
       (q3526996-list-in-domain-p domain (cdr values)))
    (equal values nil)))

(defun-sk q3526996-index-set-list-representation-p
    (index-domain index-set values)
  (forall (index)
    (and
     (true-listp values)
     (q3526996-list-in-domain-p index-domain values)
     (q3526996-valid-set-p index-domain index-set)
     (implies
      (q3526996-domain-member-p index-domain index)
      (iff
       (q3526996-set-member-p index-set index)
       (member-equal index values))))))

(defun-sk q3526996-finite-index-set-p
    (index-domain index-set)
  (exists (values)
    (q3526996-index-set-list-representation-p
     index-domain index-set values)))

(defun-sk q3526996-index-set-subset-p
    (index-domain smaller larger)
  (forall (index)
    (implies
     (and
      (q3526996-domain-member-p index-domain index)
      (q3526996-set-member-p smaller index))
     (q3526996-set-member-p larger index))))

(defun-sk q3526996-finite-coordinate-typing-p
    (spaces index-set)
  (forall (tuple index)
    (implies
     (and
      (q3526996-domain-member-p
       (q3526996-finite-product-domain spaces index-set)
       tuple)
      (q3526996-set-member-p index-set index))
     (q3526996-domain-member-p
      (q3526996-state-domain spaces index)
      (q3526996-finite-coordinate
       spaces index-set tuple index)))))

(defun-sk q3526996-full-coordinate-typing-p
    (index-domain spaces)
  (forall (tuple index)
    (implies
     (and
      (q3526996-domain-member-p
       (q3526996-full-product-domain spaces index-domain)
       tuple)
      (q3526996-domain-member-p index-domain index))
     (q3526996-domain-member-p
      (q3526996-state-domain spaces index)
      (q3526996-full-coordinate
       spaces index-domain tuple index)))))

(defun-sk q3526996-finite-coordinate-equal-p
    (spaces index-set left right)
  (forall (index)
    (implies
     (q3526996-set-member-p index-set index)
     (equal
      (q3526996-finite-coordinate
       spaces index-set left index)
      (q3526996-finite-coordinate
       spaces index-set right index)))))

(defun-sk q3526996-full-coordinate-equal-p
    (index-domain spaces left right)
  (forall (index)
    (implies
     (q3526996-domain-member-p index-domain index)
     (equal
      (q3526996-full-coordinate
       spaces index-domain left index)
      (q3526996-full-coordinate
       spaces index-domain right index)))))

(defun-sk q3526996-product-extensionality-p
    (index-domain spaces)
  (forall (index-set finite-left finite-right full-left full-right)
    (and
     (implies
      (and
       (q3526996-finite-index-set-p
        index-domain index-set)
       (q3526996-domain-member-p
        (q3526996-finite-product-domain spaces index-set)
        finite-left)
       (q3526996-domain-member-p
        (q3526996-finite-product-domain spaces index-set)
        finite-right)
       (q3526996-finite-coordinate-equal-p
        spaces index-set finite-left finite-right))
      (equal finite-left finite-right))
     (implies
      (and
       (q3526996-domain-member-p
        (q3526996-full-product-domain spaces index-domain)
        full-left)
       (q3526996-domain-member-p
        (q3526996-full-product-domain spaces index-domain)
        full-right)
       (q3526996-full-coordinate-equal-p
        index-domain spaces full-left full-right))
      (equal full-left full-right)))))

(defun-sk q3526996-finite-function-typed-p
    (spaces index-set function)
  (forall (index)
    (implies
     (q3526996-set-member-p index-set index)
     (q3526996-domain-member-p
      (q3526996-state-domain spaces index)
      (q3526996-function-at function index)))))

(defun-sk q3526996-full-function-typed-p
    (index-domain spaces function)
  (forall (index)
    (implies
     (q3526996-domain-member-p index-domain index)
     (q3526996-domain-member-p
      (q3526996-state-domain spaces index)
      (q3526996-function-at function index)))))

(defun-sk q3526996-finite-realizer-agrees-p
    (spaces index-set function tuple)
  (forall (index)
    (implies
     (q3526996-set-member-p index-set index)
     (equal
      (q3526996-finite-coordinate
       spaces index-set tuple index)
      (q3526996-function-at function index)))))

(defun-sk q3526996-full-realizer-agrees-p
    (index-domain spaces function tuple)
  (forall (index)
    (implies
     (q3526996-domain-member-p index-domain index)
     (equal
      (q3526996-full-coordinate
       spaces index-domain tuple index)
      (q3526996-function-at function index)))))

(defun-sk q3526996-finite-realizer-exists-p
    (spaces index-set function)
  (exists (tuple)
    (and
     (q3526996-domain-member-p
      (q3526996-finite-product-domain spaces index-set)
      tuple)
     (q3526996-finite-realizer-agrees-p
      spaces index-set function tuple))))

(defun-sk q3526996-full-realizer-exists-p
    (index-domain spaces function)
  (exists (tuple)
    (and
     (q3526996-domain-member-p
      (q3526996-full-product-domain spaces index-domain)
      tuple)
     (q3526996-full-realizer-agrees-p
      index-domain spaces function tuple))))

(defun-sk q3526996-product-realization-p
    (index-domain spaces)
  (forall (index-set function)
    (and
     (implies
      (and
       (q3526996-finite-index-set-p
        index-domain index-set)
       (q3526996-finite-function-typed-p
        spaces index-set function))
      (q3526996-finite-realizer-exists-p
       spaces index-set function))
     (implies
      (q3526996-full-function-typed-p
       index-domain spaces function)
      (q3526996-full-realizer-exists-p
       index-domain spaces function)))))

(defun-sk q3526996-finite-cylinder-laws-p
    (index-domain spaces index-set)
  (forall (index state-set tuple)
    (implies
     (and
      (q3526996-set-member-p index-set index)
      (q3526996-measurable-set-p
       (q3526996-state-sigma spaces index)
       state-set))
     (and
      (q3526996-measurable-set-p
       (q3526996-finite-product-sigma spaces index-set)
       (q3526996-finite-coordinate-cylinder
        spaces index-set index state-set))
      (iff
       (q3526996-set-member-p
        (q3526996-finite-coordinate-cylinder
         spaces index-set index state-set)
        tuple)
       (and
        (q3526996-domain-member-p
         (q3526996-finite-product-domain spaces index-set)
         tuple)
        (q3526996-set-member-p
         state-set
         (q3526996-finite-coordinate
          spaces index-set tuple index))))))))

(defun-sk q3526996-full-cylinder-laws-p
    (index-domain spaces)
  (forall (index state-set tuple)
    (implies
     (and
      (q3526996-domain-member-p index-domain index)
      (q3526996-measurable-set-p
       (q3526996-state-sigma spaces index)
       state-set))
     (and
      (q3526996-measurable-set-p
       (q3526996-full-product-sigma spaces index-domain)
       (q3526996-full-coordinate-cylinder
        spaces index-domain index state-set))
      (iff
       (q3526996-set-member-p
        (q3526996-full-coordinate-cylinder
         spaces index-domain index state-set)
        tuple)
       (and
        (q3526996-domain-member-p
         (q3526996-full-product-domain spaces index-domain)
         tuple)
        (q3526996-set-member-p
         state-set
         (q3526996-full-coordinate
          spaces index-domain tuple index))))))))

(defun-sk q3526996-finite-cylinders-in-sigma-p
    (spaces index-set sigma)
  (forall (index state-set)
    (implies
     (and
      (q3526996-set-member-p index-set index)
      (q3526996-measurable-set-p
       (q3526996-state-sigma spaces index)
       state-set))
     (q3526996-measurable-set-p
      sigma
      (q3526996-finite-coordinate-cylinder
       spaces index-set index state-set)))))

(defun-sk q3526996-full-cylinders-in-sigma-p
    (index-domain spaces sigma)
  (forall (index state-set)
    (implies
     (and
      (q3526996-domain-member-p index-domain index)
      (q3526996-measurable-set-p
       (q3526996-state-sigma spaces index)
       state-set))
     (q3526996-measurable-set-p
      sigma
      (q3526996-full-coordinate-cylinder
       spaces index-domain index state-set)))))

(defun-sk q3526996-finite-product-minimal-p
    (spaces index-set)
  (forall (sigma set)
    (implies
     (and
      (q3526996-sigma-algebra-p
       (q3526996-finite-product-domain spaces index-set)
       sigma)
      (q3526996-finite-cylinders-in-sigma-p
       spaces index-set sigma)
      (q3526996-measurable-set-p
       (q3526996-finite-product-sigma spaces index-set)
       set))
     (q3526996-measurable-set-p sigma set))))

(defun-sk q3526996-full-product-minimal-p
    (index-domain spaces)
  (forall (sigma set)
    (implies
     (and
      (q3526996-sigma-algebra-p
       (q3526996-full-product-domain spaces index-domain)
       sigma)
      (q3526996-full-cylinders-in-sigma-p
       index-domain spaces sigma)
      (q3526996-measurable-set-p
       (q3526996-full-product-sigma spaces index-domain)
       set))
     (q3526996-measurable-set-p sigma set))))

(defun-sk q3526996-finite-product-family-p
    (index-domain spaces)
  (forall (index-set)
    (implies
     (q3526996-finite-index-set-p
      index-domain index-set)
     (and
      (q3526996-sigma-algebra-p
       (q3526996-finite-product-domain spaces index-set)
       (q3526996-finite-product-sigma spaces index-set))
      (q3526996-finite-coordinate-typing-p
       spaces index-set)
      (q3526996-finite-cylinder-laws-p
       index-domain spaces index-set)
      (q3526996-finite-product-minimal-p
       spaces index-set)))))

(defun q3526996-product-space-interface-p
    (index-domain spaces)
  (and
   (q3526996-finite-product-family-p
    index-domain spaces)
   (q3526996-sigma-algebra-p
    (q3526996-full-product-domain spaces index-domain)
    (q3526996-full-product-sigma spaces index-domain))
   (q3526996-full-coordinate-typing-p
    index-domain spaces)
   (q3526996-full-cylinder-laws-p
    index-domain spaces)
   (q3526996-full-product-minimal-p
    index-domain spaces)
   (q3526996-product-extensionality-p
    index-domain spaces)
   (q3526996-product-realization-p
    index-domain spaces)))

;; Coordinate restrictions and their measurable inverse images.

(defun-sk q3526996-restriction-coordinate-laws-p
    (index-domain spaces)
  (forall (larger smaller tuple index full-tuple)
    (and
     (implies
      (and
       (q3526996-finite-index-set-p
        index-domain larger)
       (q3526996-finite-index-set-p
        index-domain smaller)
       (q3526996-index-set-subset-p
        index-domain smaller larger)
       (q3526996-domain-member-p
        (q3526996-finite-product-domain spaces larger)
        tuple))
      (and
       (q3526996-domain-member-p
        (q3526996-finite-product-domain spaces smaller)
        (q3526996-finite-restrict
         spaces larger smaller tuple))
       (implies
        (q3526996-set-member-p smaller index)
        (equal
         (q3526996-finite-coordinate
          spaces smaller
          (q3526996-finite-restrict
           spaces larger smaller tuple)
          index)
         (q3526996-finite-coordinate
          spaces larger tuple index)))))
     (implies
      (and
       (q3526996-finite-index-set-p
        index-domain smaller)
       (q3526996-domain-member-p
        (q3526996-full-product-domain spaces index-domain)
        full-tuple))
      (and
       (q3526996-domain-member-p
        (q3526996-finite-product-domain spaces smaller)
        (q3526996-full-restrict
         spaces index-domain smaller full-tuple))
       (implies
        (q3526996-set-member-p smaller index)
        (equal
         (q3526996-finite-coordinate
          spaces smaller
          (q3526996-full-restrict
           spaces index-domain smaller full-tuple)
          index)
         (q3526996-full-coordinate
          spaces index-domain full-tuple index))))))))

(defun-sk q3526996-finite-preimage-laws-p
    (index-domain spaces)
  (forall (larger smaller set tuple)
    (implies
     (and
      (q3526996-finite-index-set-p
       index-domain larger)
      (q3526996-finite-index-set-p
       index-domain smaller)
      (q3526996-index-set-subset-p
       index-domain smaller larger)
      (q3526996-measurable-set-p
       (q3526996-finite-product-sigma spaces smaller)
       set))
     (and
      (q3526996-measurable-set-p
       (q3526996-finite-product-sigma spaces larger)
       (q3526996-finite-restriction-preimage
        spaces larger smaller set))
      (iff
       (q3526996-set-member-p
        (q3526996-finite-restriction-preimage
         spaces larger smaller set)
        tuple)
       (and
        (q3526996-domain-member-p
         (q3526996-finite-product-domain spaces larger)
         tuple)
        (q3526996-set-member-p
         set
         (q3526996-finite-restrict
          spaces larger smaller tuple))))))))

(defun-sk q3526996-full-preimage-laws-p
    (index-domain spaces)
  (forall (index-set set tuple)
    (implies
     (and
      (q3526996-finite-index-set-p
       index-domain index-set)
      (q3526996-measurable-set-p
       (q3526996-finite-product-sigma spaces index-set)
       set))
     (and
      (q3526996-measurable-set-p
       (q3526996-full-product-sigma spaces index-domain)
       (q3526996-full-restriction-preimage
        spaces index-domain index-set set))
      (iff
       (q3526996-set-member-p
        (q3526996-full-restriction-preimage
         spaces index-domain index-set set)
        tuple)
       (and
        (q3526996-domain-member-p
         (q3526996-full-product-domain spaces index-domain)
         tuple)
        (q3526996-set-member-p
         set
         (q3526996-full-restrict
          spaces index-domain index-set tuple))))))))

(defun q3526996-restriction-interface-p
    (index-domain spaces)
  (and
   (q3526996-restriction-coordinate-laws-p
    index-domain spaces)
   (q3526996-finite-preimage-laws-p
    index-domain spaces)
   (q3526996-full-preimage-laws-p
    index-domain spaces)))

;; Projective finite-dimensional measures and projective limits.

(defun-sk q3526996-finite-measure-family-p
    (real index-domain spaces measure-family)
  (forall (index-set)
    (implies
     (q3526996-finite-index-set-p
      index-domain index-set)
     (q3526996-finite-measure-p
      real
      (q3526996-finite-product-domain spaces index-set)
      (q3526996-finite-product-sigma spaces index-set)
      (q3526996-family-measure
       measure-family index-set)))))

(defun-sk q3526996-projectively-consistent-p
    (index-domain spaces measure-family)
  (forall (larger smaller set)
    (implies
     (and
      (q3526996-finite-index-set-p
       index-domain larger)
      (q3526996-finite-index-set-p
       index-domain smaller)
      (q3526996-index-set-subset-p
       index-domain smaller larger)
      (q3526996-measurable-set-p
       (q3526996-finite-product-sigma spaces smaller)
       set))
     (equal
      (q3526996-measure-value
       (q3526996-family-measure
        measure-family larger)
       (q3526996-finite-restriction-preimage
        spaces larger smaller set))
      (q3526996-measure-value
       (q3526996-family-measure
        measure-family smaller)
       set)))))

(defun-sk q3526996-all-finite-marginals-p
    (index-domain spaces measure-family measure)
  (forall (index-set set)
    (implies
     (and
      (q3526996-finite-index-set-p
       index-domain index-set)
      (q3526996-measurable-set-p
       (q3526996-finite-product-sigma spaces index-set)
       set))
     (equal
      (q3526996-measure-value
       measure
       (q3526996-full-restriction-preimage
        spaces index-domain index-set set))
      (q3526996-measure-value
       (q3526996-family-measure
        measure-family index-set)
       set)))))

(defun q3526996-is-projective-limit-p
    (real index-domain spaces measure-family measure)
  (and
   (q3526996-finite-measure-p
    real
    (q3526996-full-product-domain spaces index-domain)
    (q3526996-full-product-sigma spaces index-domain)
    measure)
   (q3526996-all-finite-marginals-p
    index-domain spaces measure-family measure)))

(defun-sk q3526996-projective-limit-exists-p
    (real index-domain spaces measure-family)
  (exists (measure)
    (q3526996-is-projective-limit-p
     real index-domain spaces measure-family measure)))

(defun-sk
    thousand-theorems-q3526996-kolmogorov-extension-theorem-statement
    ()
  (forall (real index-domain spaces measure-family)
    (implies
     (and
      (q3526996-real-field-p real)
      (q3526996-coordinate-space-family-p
       real index-domain spaces)
      (q3526996-product-space-interface-p
       index-domain spaces)
      (q3526996-restriction-interface-p
       index-domain spaces)
      (q3526996-finite-measure-family-p
       real index-domain spaces measure-family)
      (q3526996-projectively-consistent-p
       index-domain spaces measure-family))
     (q3526996-projective-limit-exists-p
      real index-domain spaces measure-family))))

(value-triple :itpeval-statement-checked)
:q
