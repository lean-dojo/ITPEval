;; Statement-only formalization of thousand-theorems corpus artifact Q1568811,
;; "Hahn decomposition theorem": every real-valued signed measure on an
;; arbitrary measurable space admits complementary measurable positive and
;; negative sets. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Conservative interfaces present an arbitrary carrier, arbitrary subsets
;; and countable set families, a sigma algebra, and a real-valued signed
;; measure. The hypotheses below explicitly characterize the real field and
;; the VectorMeasure laws used by Lean's SignedMeasure abbreviation.

;; A Dedekind-complete ordered field, presenting the real numbers.

(defstub q1568811-r-member-p (real value) t)
(defstub q1568811-r-zero (real) t)
(defstub q1568811-r-one (real) t)
(defstub q1568811-r-add (real left right) t)
(defstub q1568811-r-multiply (real left right) t)
(defstub q1568811-r-negate (real value) t)
(defstub q1568811-r-inverse (real value) t)
(defstub q1568811-r-less (real left right) t)
(defstub q1568811-r-set-member-p (real set value) t)

(defun q1568811-r-leq (real left right)
  (not (q1568811-r-less real right left)))

(defun q1568811-r-subtract (real left right)
  (q1568811-r-add
   real left (q1568811-r-negate real right)))

(defun q1568811-r-absolute-value (real value)
  (if (q1568811-r-less
       real value (q1568811-r-zero real))
      (q1568811-r-negate real value)
    value))

(defun q1568811-r-positive-p (real value)
  (and
   (q1568811-r-member-p real value)
   (q1568811-r-less
    real (q1568811-r-zero real) value)))

(defun-sk q1568811-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1568811-r-member-p real x)
      (q1568811-r-member-p real y)
      (q1568811-r-member-p real z))
     (let* ((zero (q1568811-r-zero real))
            (one (q1568811-r-one real))
            (xy-add (q1568811-r-add real x y))
            (yz-add (q1568811-r-add real y z))
            (xy-mul (q1568811-r-multiply real x y))
            (yz-mul (q1568811-r-multiply real y z))
            (neg-x (q1568811-r-negate real x))
            (inv-x (q1568811-r-inverse real x)))
       (and
        (q1568811-r-member-p real xy-add)
        (q1568811-r-member-p real xy-mul)
        (q1568811-r-member-p real neg-x)
        (q1568811-r-member-p real inv-x)
        (equal
         (q1568811-r-add real xy-add z)
         (q1568811-r-add real x yz-add))
        (equal xy-add (q1568811-r-add real y x))
        (equal (q1568811-r-add real x zero) x)
        (equal (q1568811-r-add real x neg-x) zero)
        (equal
         (q1568811-r-multiply real xy-mul z)
         (q1568811-r-multiply real x yz-mul))
        (equal xy-mul (q1568811-r-multiply real y x))
        (equal (q1568811-r-multiply real x one) x)
        (equal (q1568811-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q1568811-r-multiply real x inv-x)
          one))
        (equal
         (q1568811-r-multiply
          real x (q1568811-r-add real y z))
         (q1568811-r-add
          real
          (q1568811-r-multiply real x y)
          (q1568811-r-multiply real x z))))))))

(defun-sk q1568811-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q1568811-r-member-p real x)
      (q1568811-r-member-p real y)
      (q1568811-r-member-p real z))
     (let ((zero (q1568811-r-zero real)))
       (and
        (not (q1568811-r-less real x x))
        (or
         (equal x y)
         (q1568811-r-less real x y)
         (q1568811-r-less real y x))
        (implies
         (and
          (q1568811-r-less real x y)
          (q1568811-r-less real y z))
         (q1568811-r-less real x z))
        (implies
         (q1568811-r-less real x y)
         (q1568811-r-less
          real
          (q1568811-r-add real x z)
          (q1568811-r-add real y z)))
        (implies
         (and
          (q1568811-r-less real zero x)
          (q1568811-r-less real zero y))
         (q1568811-r-less
          real zero
          (q1568811-r-multiply real x y))))))))

(defun-sk q1568811-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q1568811-r-member-p real x)
     (q1568811-r-set-member-p real set x))))

(defun-sk q1568811-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q1568811-r-member-p real x)
      (q1568811-r-set-member-p real set x))
     (q1568811-r-leq real x bound))))

(defun-sk q1568811-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q1568811-r-member-p real bound)
     (q1568811-r-upper-bound-p real set bound))))

(defun-sk q1568811-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q1568811-r-member-p real supremum)
     (q1568811-r-upper-bound-p real set supremum)
     (implies
      (and
       (q1568811-r-member-p real bound)
       (q1568811-r-upper-bound-p real set bound))
      (q1568811-r-leq real supremum bound)))))

(defun-sk q1568811-r-has-supremum-p (real set)
  (exists (supremum)
    (q1568811-r-supremum-p real set supremum)))

(defun-sk q1568811-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q1568811-r-set-nonempty-p real set)
      (q1568811-r-bounded-above-p real set))
     (q1568811-r-has-supremum-p real set))))

(defun q1568811-real-field-p (real)
  (let ((zero (q1568811-r-zero real))
        (one (q1568811-r-one real)))
    (and
     (q1568811-r-member-p real zero)
     (q1568811-r-member-p real one)
     (not (equal zero one))
     (q1568811-r-field-laws-p real)
     (q1568811-r-order-laws-p real)
     (q1568811-r-less real zero one)
     (q1568811-r-dedekind-complete-p real))))

;; Arbitrary subsets of an arbitrary domain and countable set families.

(defstub q1568811-domain-member-p (domain value) t)
(defstub q1568811-set-member-p (set value) t)
(defstub q1568811-set-sequence-value (sequence index) t)
(defstub q1568811-measurable-set-p (measurable set) t)
(defstub q1568811-signed-measure-value (measure set) t)

(defun-sk q1568811-valid-set-p (domain set)
  (forall (x)
    (implies
     (q1568811-set-member-p set x)
     (q1568811-domain-member-p domain x))))

(defun-sk q1568811-set-subset-p (left right)
  (forall (x)
    (implies
     (q1568811-set-member-p left x)
     (q1568811-set-member-p right x))))

(defun-sk q1568811-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q1568811-domain-member-p domain x)
     (iff
      (q1568811-set-member-p left x)
      (q1568811-set-member-p right x)))))

(defun-sk q1568811-empty-set-p (domain set)
  (forall (x)
    (iff
     (q1568811-set-member-p set x)
     (and (q1568811-domain-member-p domain x) nil))))

(defun-sk q1568811-complement-set-p
    (domain set complement)
  (forall (x)
    (iff
     (q1568811-set-member-p complement x)
     (and
      (q1568811-domain-member-p domain x)
      (not (q1568811-set-member-p set x))))))

(defun-sk q1568811-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q1568811-valid-set-p
      domain
      (q1568811-set-sequence-value sequence n)))))

(defun-sk q1568811-sequence-union-member-p
    (sequence x)
  (exists (n)
    (and
     (natp n)
     (q1568811-set-member-p
      (q1568811-set-sequence-value sequence n)
      x))))

(defun-sk q1568811-sequence-union-set-p
    (domain sequence union)
  (forall (x)
    (iff
     (q1568811-set-member-p union x)
     (and
      (q1568811-domain-member-p domain x)
      (q1568811-sequence-union-member-p sequence x)))))

(defun-sk q1568811-family-extensional-p
    (domain measurable)
  (forall (left right)
    (implies
     (q1568811-set-equiv-p domain left right)
     (iff
      (q1568811-measurable-set-p measurable left)
      (q1568811-measurable-set-p measurable right)))))

(defun-sk q1568811-family-valid-p (domain measurable)
  (forall (set)
    (implies
     (q1568811-measurable-set-p measurable set)
     (q1568811-valid-set-p domain set))))

(defun-sk q1568811-measurable-empty-exists-p
    (domain measurable)
  (exists (empty)
    (and
     (q1568811-empty-set-p domain empty)
     (q1568811-measurable-set-p measurable empty))))

(defun-sk q1568811-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q1568811-complement-set-p domain set complement)
     (q1568811-measurable-set-p measurable complement))))

(defun-sk q1568811-measurable-complements-p
    (domain measurable)
  (forall (set)
    (implies
     (q1568811-measurable-set-p measurable set)
     (q1568811-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q1568811-sequence-measurable-p
    (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q1568811-measurable-set-p
      measurable
      (q1568811-set-sequence-value sequence n)))))

(defun-sk q1568811-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q1568811-sequence-union-set-p domain sequence union)
     (q1568811-measurable-set-p measurable union))))

(defun-sk q1568811-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q1568811-set-sequence-p domain sequence)
      (q1568811-sequence-measurable-p measurable sequence))
     (q1568811-measurable-union-exists-p
      domain measurable sequence))))

(defun q1568811-sigma-algebra-p (domain measurable)
  (and
   (q1568811-family-extensional-p domain measurable)
   (q1568811-family-valid-p domain measurable)
   (q1568811-measurable-empty-exists-p domain measurable)
   (q1568811-measurable-complements-p domain measurable)
   (q1568811-measurable-sequence-unions-p
    domain measurable)))

;; Real-valued signed measures are zero off measurable sets and have the
;; epsilon-N HasSum value on every disjoint measurable countable union.

(defun-sk q1568811-disjoint-sets-p (left right)
  (forall (x)
    (not
     (and
      (q1568811-set-member-p left x)
      (q1568811-set-member-p right x)))))

(defun-sk q1568811-pairwise-disjoint-p (sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (q1568811-disjoint-sets-p
      (q1568811-set-sequence-value sequence m)
      (q1568811-set-sequence-value sequence n)))))

(defun q1568811-measure-prefix-sum
    (real measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1568811-r-zero real)
    (q1568811-r-add
     real
     (q1568811-measure-prefix-sum
      real measure sequence (1- count))
     (q1568811-signed-measure-value
      measure
      (q1568811-set-sequence-value sequence (1- count))))))

(defun-sk q1568811-series-tail-p
    (real measure sequence total epsilon start)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp start)
      (<= start count))
     (q1568811-r-less
      real
      (q1568811-r-absolute-value
       real
       (q1568811-r-subtract
        real
        (q1568811-measure-prefix-sum
         real measure sequence count)
        total))
      epsilon))))

(defun-sk q1568811-series-start-exists-p
    (real measure sequence total epsilon)
  (exists (start)
    (and
     (natp start)
     (q1568811-series-tail-p
      real measure sequence total epsilon start))))

(defun-sk q1568811-has-sum-p
    (real measure sequence total)
  (forall (epsilon)
    (implies
     (q1568811-r-positive-p real epsilon)
     (q1568811-series-start-exists-p
      real measure sequence total epsilon))))

(defun-sk q1568811-measure-extensional-p
    (domain measure)
  (forall (left right)
    (implies
     (q1568811-set-equiv-p domain left right)
     (equal
      (q1568811-signed-measure-value measure left)
      (q1568811-signed-measure-value measure right)))))

(defun-sk q1568811-measure-values-p
    (real domain measure)
  (forall (set)
    (implies
     (q1568811-valid-set-p domain set)
     (q1568811-r-member-p
      real
      (q1568811-signed-measure-value measure set)))))

(defun-sk q1568811-measure-empty-zero-p
    (real domain measure)
  (forall (empty)
    (implies
     (q1568811-empty-set-p domain empty)
     (equal
      (q1568811-signed-measure-value measure empty)
      (q1568811-r-zero real)))))

(defun-sk q1568811-nonmeasurable-zero-p
    (real domain measurable measure)
  (forall (set)
    (implies
     (and
      (q1568811-valid-set-p domain set)
      (not
       (q1568811-measurable-set-p measurable set)))
     (equal
      (q1568811-signed-measure-value measure set)
      (q1568811-r-zero real)))))

(defun-sk q1568811-countably-additive-p
    (real domain measurable measure)
  (forall (sequence union)
    (implies
     (and
      (q1568811-set-sequence-p domain sequence)
      (q1568811-sequence-measurable-p measurable sequence)
      (q1568811-pairwise-disjoint-p sequence)
      (q1568811-sequence-union-set-p domain sequence union))
     (q1568811-has-sum-p
      real measure sequence
      (q1568811-signed-measure-value measure union)))))

(defun q1568811-signed-measure-p
    (real domain measurable measure)
  (and
   (q1568811-sigma-algebra-p domain measurable)
   (q1568811-measure-extensional-p domain measure)
   (q1568811-measure-values-p real domain measure)
   (q1568811-measure-empty-zero-p real domain measure)
   (q1568811-nonmeasurable-zero-p
    real domain measurable measure)
   (q1568811-countably-additive-p
    real domain measurable measure)))

;; Positivity and negativity quantify over every measurable subset, which is
;; equivalent to the source restrictions 0 <=[i] s and s <=[j] 0 because the
;; conclusion also requires i and j themselves to be measurable.

(defun-sk q1568811-positive-set-p
    (real domain measurable measure set)
  (forall (subset)
    (implies
     (and
      (q1568811-valid-set-p domain subset)
      (q1568811-measurable-set-p measurable subset)
      (q1568811-set-subset-p subset set))
     (q1568811-r-leq
      real
      (q1568811-r-zero real)
      (q1568811-signed-measure-value measure subset)))))

(defun-sk q1568811-negative-set-p
    (real domain measurable measure set)
  (forall (subset)
    (implies
     (and
      (q1568811-valid-set-p domain subset)
      (q1568811-measurable-set-p measurable subset)
      (q1568811-set-subset-p subset set))
     (q1568811-r-leq
      real
      (q1568811-signed-measure-value measure subset)
      (q1568811-r-zero real)))))

(defun-sk q1568811-cover-domain-p (domain left right)
  (forall (x)
    (implies
     (q1568811-domain-member-p domain x)
     (or
      (q1568811-set-member-p left x)
      (q1568811-set-member-p right x)))))

(defun q1568811-is-complementary-p
    (domain left right)
  (and
   (q1568811-valid-set-p domain left)
   (q1568811-valid-set-p domain right)
   (q1568811-disjoint-sets-p left right)
   (q1568811-cover-domain-p domain left right)))

(defun q1568811-hahn-pair-p
    (real domain measurable measure positive negative)
  (and
   (q1568811-measurable-set-p measurable positive)
   (q1568811-positive-set-p
    real domain measurable measure positive)
   (q1568811-measurable-set-p measurable negative)
   (q1568811-negative-set-p
    real domain measurable measure negative)
   (q1568811-is-complementary-p
    domain positive negative)))

(defun-sk q1568811-hahn-pair-exists-p
    (real domain measurable measure)
  (exists (positive negative)
    (q1568811-hahn-pair-p
     real domain measurable measure positive negative)))

(defun-sk
    thousand-theorems-q1568811-hahn-decomposition-theorem-statement
    ()
  (forall (real domain measurable measure)
    (implies
     (and
      (q1568811-real-field-p real)
      (q1568811-signed-measure-p
       real domain measurable measure))
     (q1568811-hahn-pair-exists-p
      real domain measurable measure))))

(value-triple :itpeval-statement-checked)
:q
