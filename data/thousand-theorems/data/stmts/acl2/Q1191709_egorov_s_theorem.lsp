;; Statement-only formalization of thousand-theorems corpus artifact Q1191709,
;; "Egorov's theorem": strongly measurable functions that converge almost
;; everywhere on a measurable finite-measure set converge uniformly outside
;; an arbitrarily small measurable subset. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative application interfaces present arbitrary carriers, sets, and
;; functions without finite tables or APPLY$ tameness restrictions.  All
;; structure laws are explicit hypotheses below.  A Dedekind-complete ordered
;; field presents the reals; finite values over its nonnegative cone together
;; with a top element present the extended nonnegative reals.  DEFUN-SK keeps
;; every quantified cutoff, null set, simple-function approximation, and
;; exceptional set internal.

(defstub q1191709-apply1 (function x) t)

(defstub q1191709-apply2 (function x y) t)

(defun q1191709-member-p (carrier x)
  (if (q1191709-apply1 carrier x) t nil))

;; A presentation of the real field.

(defun-sk q1191709-real-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and (q1191709-member-p carrier x)
          (q1191709-member-p carrier y)
          (q1191709-member-p carrier z))
     (let* ((xy-add (q1191709-apply2 add x y))
            (yz-add (q1191709-apply2 add y z))
            (xy-multiply (q1191709-apply2 multiply x y))
            (yz-multiply (q1191709-apply2 multiply y z))
            (negative-x (q1191709-apply1 negate x))
            (inverse-x (q1191709-apply1 inverse x)))
       (and
        (q1191709-member-p carrier xy-add)
        (q1191709-member-p carrier xy-multiply)
        (q1191709-member-p carrier negative-x)
        (q1191709-member-p carrier inverse-x)
        (equal (q1191709-apply2 add xy-add z)
               (q1191709-apply2 add x yz-add))
        (equal xy-add (q1191709-apply2 add y x))
        (equal (q1191709-apply2 add x zero) x)
        (equal (q1191709-apply2 add x negative-x) zero)
        (equal (q1191709-apply2 multiply xy-multiply z)
               (q1191709-apply2 multiply x yz-multiply))
        (equal xy-multiply (q1191709-apply2 multiply y x))
        (equal (q1191709-apply2 multiply x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal (q1191709-apply2 multiply x inverse-x) one))
        (equal
         (q1191709-apply2 multiply x yz-add)
         (q1191709-apply2
          add
          (q1191709-apply2 multiply x y)
          (q1191709-apply2 multiply x z))))))))

(defun-sk q1191709-real-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and (q1191709-member-p carrier x)
          (q1191709-member-p carrier y)
          (q1191709-member-p carrier z))
     (and
      (not (q1191709-apply2 less x x))
      (or (equal x y)
          (q1191709-apply2 less x y)
          (q1191709-apply2 less y x))
      (implies
       (and (q1191709-apply2 less x y)
            (q1191709-apply2 less y z))
       (q1191709-apply2 less x z))
      (implies
       (q1191709-apply2 less x y)
       (q1191709-apply2
        less
        (q1191709-apply2 add x z)
        (q1191709-apply2 add y z)))
      (implies
       (and (q1191709-apply2 less zero x)
            (q1191709-apply2 less zero y))
       (q1191709-apply2
        less zero (q1191709-apply2 multiply x y)))))))

(defun-sk q1191709-real-set-valid-p (carrier set)
  (forall (x)
    (implies
     (q1191709-apply1 set x)
     (q1191709-member-p carrier x))))

(defun-sk q1191709-real-set-nonempty-p (carrier set)
  (exists (x)
    (and (q1191709-member-p carrier x)
         (q1191709-apply1 set x))))

(defun-sk q1191709-real-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and (q1191709-member-p carrier x)
          (q1191709-apply1 set x))
     (not (q1191709-apply2 less bound x)))))

(defun-sk q1191709-real-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q1191709-member-p carrier bound)
     (q1191709-real-upper-bound-p
      carrier less set bound))))

(defun-sk q1191709-real-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (q1191709-member-p carrier supremum)
     (q1191709-real-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (q1191709-member-p carrier bound)
       (q1191709-real-upper-bound-p
        carrier less set bound))
      (not (q1191709-apply2 less bound supremum))))))

(defun-sk q1191709-real-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (q1191709-real-supremum-p
     carrier less set supremum)))

(defun-sk q1191709-real-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (q1191709-real-set-valid-p carrier set)
      (q1191709-real-set-nonempty-p carrier set)
      (q1191709-real-bounded-above-p carrier less set))
     (q1191709-real-has-supremum-p
      carrier less set))))

(defun q1191709-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (q1191709-member-p carrier zero)
   (q1191709-member-p carrier one)
   (not (equal zero one))
   (q1191709-real-field-laws-p
    carrier zero one add multiply negate inverse)
   (q1191709-real-order-laws-p
    carrier zero add multiply less)
   (q1191709-apply2 less zero one)
   (q1191709-real-complete-p carrier less)))

(defun q1191709-real-leq (less left right)
  (not (q1191709-apply2 less right left)))

;; Canonical extended nonnegative reals over the presented real field.

(defun q1191709-ennreal-finite (value)
  (list :q1191709-finite value))

(defun q1191709-ennreal-top ()
  :q1191709-top)

(defun q1191709-ennreal-zero (real-zero)
  (q1191709-ennreal-finite real-zero))

(defun q1191709-ennreal-finite-p
    (real-carrier real-zero real-less value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :q1191709-finite)
   (q1191709-member-p real-carrier (cadr value))
   (q1191709-real-leq real-less real-zero (cadr value))))

(defun q1191709-ennreal-p
    (real-carrier real-zero real-less value)
  (or
   (equal value (q1191709-ennreal-top))
   (q1191709-ennreal-finite-p
    real-carrier real-zero real-less value)))

(defun q1191709-ennreal-leq
    (real-less left right)
  (cond
   ((equal right (q1191709-ennreal-top)) t)
   ((equal left (q1191709-ennreal-top)) nil)
   (t (q1191709-real-leq
       real-less (cadr left) (cadr right)))))

(defun q1191709-ennreal-less
    (real-less left right)
  (and
   (q1191709-ennreal-leq real-less left right)
   (not (equal left right))))

(defun q1191709-ennreal-add
    (real-add left right)
  (if (or (equal left (q1191709-ennreal-top))
          (equal right (q1191709-ennreal-top)))
      (q1191709-ennreal-top)
    (q1191709-ennreal-finite
     (q1191709-apply2 real-add (cadr left) (cadr right)))))

(defun q1191709-ennreal-of-real
    (real-zero real-less value)
  (if (q1191709-apply2 real-less value real-zero)
      (q1191709-ennreal-zero real-zero)
    (q1191709-ennreal-finite value)))

(defun q1191709-positive-ennreal-p
    (real-carrier real-zero real-less value)
  (and
   (q1191709-ennreal-p
    real-carrier real-zero real-less value)
   (q1191709-ennreal-less
    real-less (q1191709-ennreal-zero real-zero) value)))

;; Countable nonempty semilattice-sup index presentations.

(defun-sk q1191709-index-laws-p
    (carrier less-equal supremum)
  (forall (i j k)
    (implies
     (and (q1191709-member-p carrier i)
          (q1191709-member-p carrier j)
          (q1191709-member-p carrier k))
     (let ((ij (q1191709-apply2 supremum i j)))
       (and
        (q1191709-member-p carrier ij)
        (q1191709-apply2 less-equal i i)
        (implies
         (and (q1191709-apply2 less-equal i j)
              (q1191709-apply2 less-equal j k))
         (q1191709-apply2 less-equal i k))
        (implies
         (and (q1191709-apply2 less-equal i j)
              (q1191709-apply2 less-equal j i))
         (equal i j))
        (q1191709-apply2 less-equal i ij)
        (q1191709-apply2 less-equal j ij)
        (implies
         (and (q1191709-apply2 less-equal i k)
              (q1191709-apply2 less-equal j k))
         (q1191709-apply2 less-equal ij k)))))))

(defun-sk q1191709-index-nonempty-p (carrier)
  (exists (i)
    (q1191709-member-p carrier i)))

(defun-sk q1191709-index-enumeration-witness-exists-p
    (enumeration i)
  (exists (n)
    (and
     (natp n)
     (equal (q1191709-apply1 enumeration n) i))))

(defun-sk q1191709-index-enumeration-covers-p
    (carrier enumeration)
  (forall (i)
    (implies
     (q1191709-member-p carrier i)
     (q1191709-index-enumeration-witness-exists-p
      enumeration i))))

(defun-sk q1191709-index-enumeration-values-p
    (carrier enumeration)
  (forall (n)
    (implies
     (natp n)
     (q1191709-member-p
      carrier (q1191709-apply1 enumeration n)))))

(defun q1191709-countable-semilattice-sup-p
    (carrier less-equal supremum enumeration)
  (and
   (q1191709-index-laws-p carrier less-equal supremum)
   (q1191709-index-nonempty-p carrier)
   (q1191709-index-enumeration-values-p carrier enumeration)
   (q1191709-index-enumeration-covers-p carrier enumeration)))

;; Arbitrary subsets of the point carrier and a sigma algebra on them.

(defun-sk q1191709-set-p (point-carrier set)
  (forall (x)
    (implies
     (q1191709-apply1 set x)
     (q1191709-member-p point-carrier x))))

(defun-sk q1191709-set-equivalent-p
    (point-carrier left right)
  (forall (x)
    (implies
     (q1191709-member-p point-carrier x)
     (iff (q1191709-apply1 left x)
          (q1191709-apply1 right x)))))

(defun-sk q1191709-subset-p
    (point-carrier left right)
  (forall (x)
    (implies
     (and
      (q1191709-member-p point-carrier x)
      (q1191709-apply1 left x))
     (q1191709-apply1 right x))))

(defun-sk q1191709-empty-set-p
    (point-carrier set)
  (forall (x)
    (implies
     (q1191709-member-p point-carrier x)
     (not (q1191709-apply1 set x)))))

(defun-sk q1191709-complement-of-p
    (point-carrier set complement)
  (forall (x)
    (implies
     (q1191709-member-p point-carrier x)
     (iff
      (q1191709-apply1 complement x)
      (not (q1191709-apply1 set x))))))

(defun-sk q1191709-family-values-are-sets-p
    (point-carrier family)
  (forall (n)
    (implies
     (natp n)
     (q1191709-set-p
      point-carrier (q1191709-apply1 family n)))))

(defun-sk q1191709-family-member-exists-p
    (family x)
  (exists (n)
    (and
     (natp n)
     (q1191709-apply1
      (q1191709-apply1 family n) x))))

(defun-sk q1191709-union-of-family-p
    (point-carrier family union)
  (forall (x)
    (implies
     (q1191709-member-p point-carrier x)
     (iff
      (q1191709-apply1 union x)
      (q1191709-family-member-exists-p family x)))))

(defun-sk q1191709-family-measurable-p
    (measurable-set-p family)
  (forall (n)
    (implies
     (natp n)
     (q1191709-apply1
      measurable-set-p (q1191709-apply1 family n)))))

(defun-sk q1191709-measurable-set-extensional-p
    (point-carrier measurable-set-p)
  (forall (left right)
    (implies
     (and
      (q1191709-set-p point-carrier left)
      (q1191709-set-p point-carrier right)
      (q1191709-set-equivalent-p
       point-carrier left right)
      (q1191709-apply1 measurable-set-p left))
     (q1191709-apply1 measurable-set-p right))))

(defun-sk q1191709-measurable-empty-set-exists-p
    (point-carrier measurable-set-p)
  (exists (empty)
    (and
     (q1191709-set-p point-carrier empty)
     (q1191709-empty-set-p point-carrier empty)
     (q1191709-apply1 measurable-set-p empty))))

(defun-sk q1191709-measurable-complement-exists-p
    (point-carrier measurable-set-p set)
  (exists (complement)
    (and
     (q1191709-set-p point-carrier complement)
     (q1191709-complement-of-p
      point-carrier set complement)
     (q1191709-apply1 measurable-set-p complement))))

(defun-sk q1191709-measurable-union-exists-p
    (point-carrier measurable-set-p family)
  (exists (union)
    (and
     (q1191709-set-p point-carrier union)
     (q1191709-union-of-family-p
      point-carrier family union)
     (q1191709-apply1 measurable-set-p union))))

(defun-sk q1191709-measurable-space-laws-p
    (point-carrier measurable-set-p)
  (forall (set family)
    (and
     (implies
      (q1191709-apply1 measurable-set-p set)
      (q1191709-set-p point-carrier set))
     (implies
      (q1191709-apply1 measurable-set-p set)
      (q1191709-measurable-complement-exists-p
       point-carrier measurable-set-p set))
     (implies
      (and
       (q1191709-family-values-are-sets-p
        point-carrier family)
       (q1191709-family-measurable-p
        measurable-set-p family))
      (q1191709-measurable-union-exists-p
       point-carrier measurable-set-p family)))))

(defun q1191709-measurable-space-p
    (point-carrier measurable-set-p)
  (and
   (q1191709-measurable-set-extensional-p
    point-carrier measurable-set-p)
   (q1191709-measurable-empty-set-exists-p
    point-carrier measurable-set-p)
   (q1191709-measurable-space-laws-p
    point-carrier measurable-set-p)))

;; Measures are extensional, zero on empty sets, and countably additive on
;; disjoint measurable families.  Infinite sums are least upper bounds of
;; their finite partial sums in the canonical extended nonnegative reals.

(defun-sk q1191709-family-pairwise-disjoint-p
    (point-carrier family)
  (forall (m n x)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n))
      (q1191709-member-p point-carrier x))
     (not
      (and
       (q1191709-apply1 (q1191709-apply1 family m) x)
       (q1191709-apply1 (q1191709-apply1 family n) x))))))

(defun q1191709-measure-partial-sum
    (real-zero real-add measure family count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1191709-ennreal-zero real-zero)
    (q1191709-ennreal-add
     real-add
     (q1191709-measure-partial-sum
      real-zero real-add measure family (1- count))
     (q1191709-apply1
      measure (q1191709-apply1 family (1- count))))))

(defun-sk q1191709-measure-series-upper-bound-p
    (real-zero real-add real-less measure family bound)
  (forall (count)
    (implies
     (natp count)
     (q1191709-ennreal-leq
      real-less
      (q1191709-measure-partial-sum
       real-zero real-add measure family count)
      bound))))

(defun-sk q1191709-measure-series-sum-p
    (real-carrier real-zero real-add real-less
     measure family total)
  (forall (bound)
    (and
     (q1191709-ennreal-p
      real-carrier real-zero real-less total)
     (q1191709-measure-series-upper-bound-p
      real-zero real-add real-less measure family total)
     (implies
      (and
       (q1191709-ennreal-p
        real-carrier real-zero real-less bound)
       (q1191709-measure-series-upper-bound-p
        real-zero real-add real-less measure family bound))
      (q1191709-ennreal-leq real-less total bound)))))

(defun-sk q1191709-measure-laws-p
    (real-carrier real-zero real-add real-less
     point-carrier measurable-set-p measure)
  (forall (set left right family union)
    (and
     (implies
      (q1191709-set-p point-carrier set)
      (q1191709-ennreal-p
       real-carrier real-zero real-less
       (q1191709-apply1 measure set)))
     (implies
      (and
       (q1191709-set-p point-carrier left)
       (q1191709-set-p point-carrier right)
       (q1191709-set-equivalent-p
        point-carrier left right))
      (equal
       (q1191709-apply1 measure left)
       (q1191709-apply1 measure right)))
     (implies
      (and
       (q1191709-set-p point-carrier set)
       (q1191709-empty-set-p point-carrier set))
      (equal
       (q1191709-apply1 measure set)
       (q1191709-ennreal-zero real-zero)))
     (implies
      (and
       (q1191709-family-values-are-sets-p
        point-carrier family)
       (q1191709-family-measurable-p
        measurable-set-p family)
       (q1191709-family-pairwise-disjoint-p
        point-carrier family)
       (q1191709-set-p point-carrier union)
       (q1191709-union-of-family-p
        point-carrier family union))
      (q1191709-measure-series-sum-p
       real-carrier real-zero real-add real-less
       measure family (q1191709-apply1 measure union))))))

(defun q1191709-measure-space-p
    (real-carrier real-zero real-add real-less
     point-carrier measurable-set-p measure)
  (and
   (q1191709-measurable-space-p
    point-carrier measurable-set-p)
   (q1191709-measure-laws-p
    real-carrier real-zero real-add real-less
    point-carrier measurable-set-p measure)))

;; The codomain is an arbitrary pseudo-emetric space.

(defun-sk q1191709-pseudo-emetric-laws-p
    (real-carrier real-zero real-add real-less
     value-carrier edistance)
  (forall (x y z)
    (implies
     (and
      (q1191709-member-p value-carrier x)
      (q1191709-member-p value-carrier y)
      (q1191709-member-p value-carrier z))
     (let ((dxy (q1191709-apply2 edistance x y))
           (dyz (q1191709-apply2 edistance y z))
           (dxz (q1191709-apply2 edistance x z)))
       (and
        (q1191709-ennreal-p
         real-carrier real-zero real-less dxy)
        (q1191709-ennreal-p
         real-carrier real-zero real-less dyz)
        (q1191709-ennreal-p
         real-carrier real-zero real-less dxz)
        (equal
         (q1191709-apply2 edistance x x)
         (q1191709-ennreal-zero real-zero))
        (equal dxy (q1191709-apply2 edistance y x))
        (q1191709-ennreal-leq
         real-less dxz
         (q1191709-ennreal-add real-add dxy dyz)))))))

(defun q1191709-pseudo-emetric-space-p
    (real-carrier real-zero real-add real-less
     value-carrier edistance)
  (q1191709-pseudo-emetric-laws-p
   real-carrier real-zero real-add real-less
   value-carrier edistance))

;; Pointwise convergence along atTop of the arbitrary directed index order.

(defun-sk q1191709-pointwise-tail-p
    (real-less index-carrier index-less-equal
     point value sequence limit edistance radius cutoff)
  (forall (index)
    (implies
     (and
      (q1191709-member-p index-carrier index)
      (q1191709-apply2 index-less-equal cutoff index))
     (q1191709-ennreal-less
      real-less
      (q1191709-apply2
       edistance
       (q1191709-apply2 sequence index point)
       (q1191709-apply1 limit point))
      radius))))

(defun-sk q1191709-pointwise-cutoff-exists-p
    (real-less index-carrier index-less-equal
     point value sequence limit edistance radius)
  (exists (cutoff)
    (and
     (q1191709-member-p index-carrier cutoff)
     (q1191709-pointwise-tail-p
      real-less index-carrier index-less-equal
      point value sequence limit edistance radius cutoff))))

(defun-sk q1191709-pointwise-converges-p
    (real-carrier real-zero real-less
     index-carrier index-less-equal
     point value sequence limit edistance)
  (forall (radius)
    (implies
     (q1191709-positive-ennreal-p
      real-carrier real-zero real-less radius)
     (q1191709-pointwise-cutoff-exists-p
      real-less index-carrier index-less-equal
      point value sequence limit edistance radius))))

;; Strong measurability is expressed by pointwise limits of measurable simple
;; functions.  Each simple function has an internally supplied finite range,
;; and each fiber is an internally supplied measurable set.

(defun q1191709-value-list-p (value-carrier values)
  (if (consp values)
      (and
       (q1191709-member-p value-carrier (car values))
       (q1191709-value-list-p value-carrier (cdr values)))
    (equal values nil)))

(defun-sk q1191709-simple-values-p
    (point-carrier value-carrier approximation ranges n)
  (forall (x)
    (implies
     (q1191709-member-p point-carrier x)
     (and
      (q1191709-member-p
       value-carrier (q1191709-apply2 approximation n x))
      (member-equal
       (q1191709-apply2 approximation n x)
       (q1191709-apply1 ranges n))))))

(defun-sk q1191709-fiber-set-p
    (point-carrier approximation n value fiber)
  (forall (x)
    (implies
     (q1191709-member-p point-carrier x)
     (iff
      (q1191709-apply1 fiber x)
      (equal
       (q1191709-apply2 approximation n x)
       value)))))

(defun-sk q1191709-measurable-fiber-exists-p
    (point-carrier measurable-set-p approximation n value)
  (exists (fiber)
    (and
     (q1191709-set-p point-carrier fiber)
     (q1191709-apply1 measurable-set-p fiber)
     (q1191709-fiber-set-p
      point-carrier approximation n value fiber))))

(defun q1191709-simple-fibers-measurable-p
    (point-carrier measurable-set-p approximation n values)
  (if (consp values)
      (and
       (q1191709-measurable-fiber-exists-p
        point-carrier measurable-set-p
        approximation n (car values))
       (q1191709-simple-fibers-measurable-p
        point-carrier measurable-set-p
        approximation n (cdr values)))
    (equal values nil)))

(defun-sk q1191709-simple-approximations-p
    (point-carrier value-carrier measurable-set-p
     approximation ranges)
  (forall (n)
    (implies
     (natp n)
     (let ((values (q1191709-apply1 ranges n)))
       (and
        (true-listp values)
        (q1191709-value-list-p value-carrier values)
        (q1191709-simple-values-p
         point-carrier value-carrier
         approximation ranges n)
        (q1191709-simple-fibers-measurable-p
         point-carrier measurable-set-p
         approximation n values))))))

(defun-sk q1191709-natural-tail-p
    (real-less point target approximation edistance radius cutoff)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (q1191709-ennreal-less
      real-less
      (q1191709-apply2
       edistance
       (q1191709-apply2 approximation n point)
       target)
      radius))))

(defun-sk q1191709-natural-cutoff-exists-p
    (real-less point target approximation edistance radius)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1191709-natural-tail-p
      real-less point target approximation
      edistance radius cutoff))))

(defun-sk q1191709-natural-converges-p
    (real-carrier real-zero real-less
     point target approximation edistance)
  (forall (radius)
    (implies
     (q1191709-positive-ennreal-p
      real-carrier real-zero real-less radius)
     (q1191709-natural-cutoff-exists-p
      real-less point target approximation
      edistance radius))))

(defun-sk q1191709-approximation-converges-to-function-p
    (real-carrier real-zero real-less
     point-carrier function approximation edistance)
  (forall (point)
    (implies
     (q1191709-member-p point-carrier point)
     (q1191709-natural-converges-p
      real-carrier real-zero real-less
      point (q1191709-apply1 function point)
      approximation edistance))))

(defun-sk q1191709-strongly-measurable-function-p
    (real-carrier real-zero real-less
     point-carrier value-carrier measurable-set-p
     function edistance)
  (exists (approximation ranges)
    (and
     (q1191709-simple-approximations-p
      point-carrier value-carrier measurable-set-p
      approximation ranges)
     (q1191709-approximation-converges-to-function-p
      real-carrier real-zero real-less
      point-carrier function approximation edistance))))

(defun-sk q1191709-approximation-converges-to-section-p
    (real-carrier real-zero real-less
     point-carrier index sequence approximation edistance)
  (forall (point)
    (implies
     (q1191709-member-p point-carrier point)
     (q1191709-natural-converges-p
      real-carrier real-zero real-less
      point (q1191709-apply2 sequence index point)
      approximation edistance))))

(defun-sk q1191709-strongly-measurable-section-p
    (real-carrier real-zero real-less
     point-carrier value-carrier measurable-set-p
     sequence index edistance)
  (exists (approximation ranges)
    (and
     (q1191709-simple-approximations-p
      point-carrier value-carrier measurable-set-p
      approximation ranges)
     (q1191709-approximation-converges-to-section-p
      real-carrier real-zero real-less
      point-carrier index sequence approximation edistance))))

(defun-sk q1191709-all-sections-strongly-measurable-p
    (real-carrier real-zero real-less
     point-carrier value-carrier measurable-set-p
     index-carrier sequence edistance)
  (forall (index)
    (implies
     (q1191709-member-p index-carrier index)
     (q1191709-strongly-measurable-section-p
      real-carrier real-zero real-less
      point-carrier value-carrier measurable-set-p
      sequence index edistance))))

;; Function typing, almost-everywhere convergence, and uniform convergence.

(defun-sk q1191709-function-types-p
    (index-carrier point-carrier value-carrier sequence limit)
  (forall (index point)
    (and
     (implies
      (and
       (q1191709-member-p index-carrier index)
       (q1191709-member-p point-carrier point))
      (q1191709-member-p
       value-carrier (q1191709-apply2 sequence index point)))
     (implies
      (q1191709-member-p point-carrier point)
      (q1191709-member-p
       value-carrier (q1191709-apply1 limit point))))))

(defun-sk q1191709-converges-outside-null-set-p
    (real-carrier real-zero real-less
     index-carrier index-less-equal point-carrier
     set exceptional sequence limit edistance)
  (forall (point)
    (implies
     (and
      (q1191709-member-p point-carrier point)
      (not (q1191709-apply1 exceptional point))
      (q1191709-apply1 set point))
     (q1191709-pointwise-converges-p
      real-carrier real-zero real-less
      index-carrier index-less-equal
      point nil sequence limit edistance))))

(defun-sk q1191709-null-set-exists-p
    (real-carrier real-zero real-less
     index-carrier index-less-equal point-carrier
     measurable-set-p measure set sequence limit edistance)
  (exists (exceptional)
    (and
     (q1191709-set-p point-carrier exceptional)
     (q1191709-apply1 measurable-set-p exceptional)
     (equal
      (q1191709-apply1 measure exceptional)
      (q1191709-ennreal-zero real-zero))
     (q1191709-converges-outside-null-set-p
      real-carrier real-zero real-less
      index-carrier index-less-equal point-carrier
      set exceptional sequence limit edistance))))

(defun-sk q1191709-uniform-tail-p
    (real-less index-carrier index-less-equal
     point-carrier set exceptional
     sequence limit edistance radius cutoff)
  (forall (index point)
    (implies
     (and
      (q1191709-member-p index-carrier index)
      (q1191709-apply2 index-less-equal cutoff index)
      (q1191709-member-p point-carrier point)
      (q1191709-apply1 set point)
      (not (q1191709-apply1 exceptional point)))
     (q1191709-ennreal-less
      real-less
      (q1191709-apply2
       edistance
       (q1191709-apply2 sequence index point)
       (q1191709-apply1 limit point))
      radius))))

(defun-sk q1191709-uniform-cutoff-exists-p
    (real-less index-carrier index-less-equal
     point-carrier set exceptional
     sequence limit edistance radius)
  (exists (cutoff)
    (and
     (q1191709-member-p index-carrier cutoff)
     (q1191709-uniform-tail-p
      real-less index-carrier index-less-equal
      point-carrier set exceptional
      sequence limit edistance radius cutoff))))

(defun-sk q1191709-uniformly-converges-off-p
    (real-carrier real-zero real-less
     index-carrier index-less-equal point-carrier
     set exceptional sequence limit edistance)
  (forall (radius)
    (implies
     (q1191709-positive-ennreal-p
      real-carrier real-zero real-less radius)
     (q1191709-uniform-cutoff-exists-p
      real-less index-carrier index-less-equal
      point-carrier set exceptional
      sequence limit edistance radius))))

(defun-sk q1191709-exceptional-set-exists-p
    (real-carrier real-zero real-less
     index-carrier index-less-equal point-carrier
     measurable-set-p measure set sequence limit edistance epsilon)
  (exists (exceptional)
    (and
     (q1191709-set-p point-carrier exceptional)
     (q1191709-subset-p point-carrier exceptional set)
     (q1191709-apply1 measurable-set-p exceptional)
     (q1191709-ennreal-leq
      real-less
      (q1191709-apply1 measure exceptional)
      (q1191709-ennreal-of-real
       real-zero real-less epsilon))
     (q1191709-uniformly-converges-off-p
      real-carrier real-zero real-less
      index-carrier index-less-equal point-carrier
      set exceptional sequence limit edistance))))

(defun-sk thousand-theorems-q1191709-egorov-s-theorem-statement ()
  (forall
      (real-carrier real-zero real-one real-add real-multiply
       real-negate real-inverse real-less
       index-carrier index-less-equal index-supremum index-enumeration
       point-carrier measurable-set-p measure
       value-carrier edistance sequence limit set epsilon)
    (implies
     (and
      (q1191709-real-field-p
       real-carrier real-zero real-one real-add real-multiply
       real-negate real-inverse real-less)
      (q1191709-countable-semilattice-sup-p
       index-carrier index-less-equal
       index-supremum index-enumeration)
      (q1191709-measure-space-p
       real-carrier real-zero real-add real-less
       point-carrier measurable-set-p measure)
      (q1191709-pseudo-emetric-space-p
       real-carrier real-zero real-add real-less
       value-carrier edistance)
      (q1191709-set-p point-carrier set)
      (q1191709-function-types-p
       index-carrier point-carrier value-carrier sequence limit)
      (q1191709-all-sections-strongly-measurable-p
       real-carrier real-zero real-less
       point-carrier value-carrier measurable-set-p
       index-carrier sequence edistance)
      (q1191709-strongly-measurable-function-p
       real-carrier real-zero real-less
       point-carrier value-carrier measurable-set-p
       limit edistance)
      (q1191709-apply1 measurable-set-p set)
      (not
       (equal
        (q1191709-apply1 measure set)
        (q1191709-ennreal-top)))
      (q1191709-null-set-exists-p
       real-carrier real-zero real-less
       index-carrier index-less-equal point-carrier
       measurable-set-p measure set sequence limit edistance)
      (q1191709-member-p real-carrier epsilon)
      (q1191709-apply2 real-less real-zero epsilon))
     (q1191709-exceptional-set-exists-p
      real-carrier real-zero real-less
      index-carrier index-less-equal point-carrier
      measurable-set-p measure set sequence limit edistance epsilon))))

(value-triple :itpeval-statement-checked)
:q
