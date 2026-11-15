;; Statement-only formalization of thousand-theorems corpus artifact Q137164,
;; "Besicovitch covering theorem": in a second-countable measurable metric
;; space with the Besicovitch covering property, arbitrarily small admissible
;; radii yield a countable pairwise-disjoint closed-ball covering almost all
;; of a set, with each radius below its prescribed positive bound.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, sets, functions, and relations are represented by tame
;; APPLY$ function objects.  DEFUN-SK keeps all mathematical quantifiers,
;; including the covering set and radius function, internal to the statement.
;; A Dedekind-complete ordered field presents the reals, and its nonnegative
;; cone with a top element presents the extended nonnegative reals.

(defun q137164-apply1 (function x)
  (apply$ function (list x)))

(defun q137164-apply2 (function x y)
  (apply$ function (list x y)))

(defun q137164-member-p (carrier x)
  (and
   (tamep-functionp carrier)
   (if (q137164-apply1 carrier x) t nil)))

(defun q137164-real-leq (less left right)
  (not (q137164-apply2 less right left)))

;; A Dedekind-complete ordered field.

(defun-sk q137164-real-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (q137164-member-p carrier x)
      (q137164-member-p carrier y)
      (q137164-member-p carrier z))
     (let* ((xy-add (q137164-apply2 add x y))
            (yz-add (q137164-apply2 add y z))
            (xy-mul (q137164-apply2 multiply x y))
            (yz-mul (q137164-apply2 multiply y z))
            (neg-x (q137164-apply1 negate x))
            (inv-x (q137164-apply1 inverse x)))
       (and
        (q137164-member-p carrier xy-add)
        (q137164-member-p carrier xy-mul)
        (q137164-member-p carrier neg-x)
        (q137164-member-p carrier inv-x)
        (equal (q137164-apply2 add xy-add z)
               (q137164-apply2 add x yz-add))
        (equal xy-add (q137164-apply2 add y x))
        (equal (q137164-apply2 add x zero) x)
        (equal (q137164-apply2 add x neg-x) zero)
        (equal (q137164-apply2 multiply xy-mul z)
               (q137164-apply2 multiply x yz-mul))
        (equal xy-mul (q137164-apply2 multiply y x))
        (equal (q137164-apply2 multiply x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (q137164-apply2 multiply x inv-x) one))
        (equal
         (q137164-apply2 multiply x yz-add)
         (q137164-apply2
          add
          (q137164-apply2 multiply x y)
          (q137164-apply2 multiply x z))))))))

(defun-sk q137164-real-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (q137164-member-p carrier x)
      (q137164-member-p carrier y)
      (q137164-member-p carrier z))
     (and
      (not (q137164-apply2 less x x))
      (or
       (equal x y)
       (q137164-apply2 less x y)
       (q137164-apply2 less y x))
      (implies
       (and
        (q137164-apply2 less x y)
        (q137164-apply2 less y z))
       (q137164-apply2 less x z))
      (implies
       (q137164-apply2 less x y)
       (q137164-apply2
        less
        (q137164-apply2 add x z)
        (q137164-apply2 add y z)))
      (implies
       (and
        (q137164-apply2 less zero x)
        (q137164-apply2 less zero y))
       (q137164-apply2
        less zero (q137164-apply2 multiply x y)))))))

(defun-sk q137164-real-set-values-p (carrier set)
  (forall (x)
    (implies
     (q137164-apply1 set x)
     (q137164-member-p carrier x))))

(defun q137164-real-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q137164-real-set-values-p carrier set)))

(defun-sk q137164-real-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (q137164-member-p carrier x)
     (q137164-apply1 set x))))

(defun-sk q137164-real-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (q137164-member-p carrier x)
      (q137164-apply1 set x))
     (q137164-real-leq less x bound))))

(defun-sk q137164-real-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q137164-member-p carrier bound)
     (q137164-real-upper-bound-p
      carrier less set bound))))

(defun-sk q137164-real-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (q137164-member-p carrier supremum)
     (q137164-real-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (q137164-member-p carrier bound)
       (q137164-real-upper-bound-p
        carrier less set bound))
      (q137164-real-leq less supremum bound)))))

(defun-sk q137164-real-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (q137164-real-supremum-p
     carrier less set supremum)))

(defun-sk q137164-real-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (q137164-real-set-p carrier set)
      (q137164-real-set-nonempty-p carrier set)
      (q137164-real-bounded-above-p carrier less set))
     (q137164-real-has-supremum-p
      carrier less set))))

(defun q137164-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (q137164-member-p carrier zero)
   (q137164-member-p carrier one)
   (not (equal zero one))
   (q137164-real-field-laws-p
    carrier zero one add multiply negate inverse)
   (q137164-real-order-laws-p
    carrier zero add multiply less)
   (q137164-apply2 less zero one)
   (q137164-real-complete-p carrier less)))

;; Arbitrary subsets and functions.

(defun-sk q137164-set-values-p (carrier set)
  (forall (x)
    (implies
     (q137164-apply1 set x)
     (q137164-member-p carrier x))))

(defun q137164-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q137164-set-values-p carrier set)))

(defun-sk q137164-set-equivalent-p
    (carrier left right)
  (forall (x)
    (implies
     (q137164-member-p carrier x)
     (iff
      (q137164-apply1 left x)
      (q137164-apply1 right x)))))

(defun-sk q137164-subset-p
    (carrier left right)
  (forall (x)
    (implies
     (and
      (q137164-member-p carrier x)
      (q137164-apply1 left x))
     (q137164-apply1 right x))))

(defun-sk q137164-empty-set-p (carrier set)
  (forall (x)
    (implies
     (q137164-member-p carrier x)
     (not (q137164-apply1 set x)))))

(defun-sk q137164-complement-of-p
    (carrier set complement)
  (forall (x)
    (implies
     (q137164-member-p carrier x)
     (iff
      (q137164-apply1 complement x)
      (not (q137164-apply1 set x))))))

(defun-sk q137164-function-values-p
    (domain-carrier codomain-carrier function)
  (forall (x)
    (implies
     (q137164-member-p domain-carrier x)
     (q137164-member-p
      codomain-carrier (q137164-apply1 function x)))))

(defun q137164-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (q137164-function-values-p
    domain-carrier codomain-carrier function)))

(defun-sk q137164-set-sequence-values-p
    (carrier family)
  (forall (n)
    (implies
     (natp n)
     (q137164-set-p
      carrier (q137164-apply1 family n)))))

(defun q137164-set-sequence-p (carrier family)
  (and
   (tamep-functionp family)
   (q137164-set-sequence-values-p carrier family)))

(defun-sk q137164-family-member-exists-p
    (family x)
  (exists (n)
    (and
     (natp n)
     (q137164-apply1
      (q137164-apply1 family n) x))))

(defun-sk q137164-union-of-family-p
    (carrier family union)
  (forall (x)
    (implies
     (q137164-member-p carrier x)
     (iff
      (q137164-apply1 union x)
      (q137164-family-member-exists-p family x)))))

(defun-sk q137164-family-measurable-p
    (measurable family)
  (forall (n)
    (implies
     (natp n)
     (q137164-apply1
      measurable (q137164-apply1 family n)))))

(defun-sk q137164-family-pairwise-disjoint-p
    (carrier family)
  (forall (m n x)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n))
      (q137164-member-p carrier x))
     (not
      (and
       (q137164-apply1 (q137164-apply1 family m) x)
       (q137164-apply1 (q137164-apply1 family n) x))))))

;; The metric structure and its induced topology.

(defun-sk q137164-metric-laws-p
    (real-carrier real-zero real-add real-less
     point-carrier distance)
  (forall (x y z)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-member-p point-carrier y)
      (q137164-member-p point-carrier z))
     (let ((dxy (q137164-apply2 distance x y))
           (dyz (q137164-apply2 distance y z))
           (dxz (q137164-apply2 distance x z)))
       (and
        (q137164-member-p real-carrier dxy)
        (q137164-member-p real-carrier dyz)
        (q137164-member-p real-carrier dxz)
        (q137164-real-leq real-less real-zero dxy)
        (iff (equal dxy real-zero) (equal x y))
        (equal dxy (q137164-apply2 distance y x))
        (q137164-real-leq
         real-less dxz
         (q137164-apply2 real-add dxy dyz)))))))

(defun q137164-metric-space-p
    (real-carrier real-zero real-add real-less
     point-carrier distance)
  (and
   (tamep-functionp point-carrier)
   (tamep-functionp distance)
   (q137164-metric-laws-p
    real-carrier real-zero real-add real-less
    point-carrier distance)))

(defun-sk q137164-open-ball-contained-p
    (real-less point-carrier distance set center radius)
  (forall (y)
    (implies
     (and
      (q137164-member-p point-carrier y)
      (q137164-apply2
       real-less
       (q137164-apply2 distance center y)
       radius))
     (q137164-apply1 set y))))

(defun-sk q137164-open-radius-exists-p
    (real-carrier real-zero real-less
     point-carrier distance set center)
  (exists (radius)
    (and
     (q137164-member-p real-carrier radius)
     (q137164-apply2 real-less real-zero radius)
     (q137164-open-ball-contained-p
      real-less point-carrier distance
      set center radius))))

(defun-sk q137164-metric-open-points-p
    (real-carrier real-zero real-less
     point-carrier distance set)
  (forall (x)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-apply1 set x))
     (q137164-open-radius-exists-p
      real-carrier real-zero real-less
      point-carrier distance set x))))

(defun q137164-metric-open-set-p
    (real-carrier real-zero real-less
     point-carrier distance set)
  (and
   (q137164-set-p point-carrier set)
   (q137164-metric-open-points-p
    real-carrier real-zero real-less
    point-carrier distance set)))

(defun-sk q137164-basis-active-indices-p (active)
  (forall (index)
    (implies
     (q137164-apply1 active index)
     (natp index))))

(defun-sk q137164-basis-section-values-p
    (point-carrier basis index)
  (forall (x)
    (implies
     (q137164-apply2 basis index x)
     (q137164-member-p point-carrier x))))

(defun-sk q137164-basis-ball-contained-p
    (real-less point-carrier distance basis index center radius)
  (forall (y)
    (implies
     (and
      (q137164-member-p point-carrier y)
      (q137164-apply2
       real-less
       (q137164-apply2 distance center y)
       radius))
     (q137164-apply2 basis index y))))

(defun-sk q137164-basis-open-radius-exists-p
    (real-carrier real-zero real-less
     point-carrier distance basis index center)
  (exists (radius)
    (and
     (q137164-member-p real-carrier radius)
     (q137164-apply2 real-less real-zero radius)
     (q137164-basis-ball-contained-p
      real-less point-carrier distance
      basis index center radius))))

(defun-sk q137164-basis-section-open-p
    (real-carrier real-zero real-less
     point-carrier distance basis index)
  (forall (x)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-apply2 basis index x))
     (q137164-basis-open-radius-exists-p
      real-carrier real-zero real-less
      point-carrier distance basis index x))))

(defun-sk q137164-basis-sections-p
    (real-carrier real-zero real-less
     point-carrier distance basis active)
  (forall (index)
    (implies
     (and
      (natp index)
      (q137164-apply1 active index))
     (and
      (q137164-basis-section-values-p
       point-carrier basis index)
      (q137164-basis-section-open-p
       real-carrier real-zero real-less
       point-carrier distance basis index)))))

(defun-sk q137164-basis-section-subset-p
    (point-carrier basis index set)
  (forall (x)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-apply2 basis index x))
     (q137164-apply1 set x))))

(defun-sk q137164-basis-hit-exists-p
    (point-carrier basis active set x)
  (exists (index)
    (and
     (natp index)
     (q137164-apply1 active index)
     (q137164-apply2 basis index x)
     (q137164-basis-section-subset-p
      point-carrier basis index set))))

(defun-sk q137164-basis-law-p
    (real-carrier real-zero real-less
     point-carrier distance basis active)
  (forall (set x)
    (implies
     (and
      (q137164-metric-open-set-p
       real-carrier real-zero real-less
       point-carrier distance set)
      (q137164-member-p point-carrier x)
      (q137164-apply1 set x))
     (q137164-basis-hit-exists-p
      point-carrier basis active set x))))

(defun q137164-second-countable-witness-p
    (real-carrier real-zero real-less
     point-carrier distance basis active)
  (and
   (tamep-functionp basis)
   (tamep-functionp active)
   (q137164-basis-active-indices-p active)
   (q137164-basis-sections-p
    real-carrier real-zero real-less
    point-carrier distance basis active)
   (q137164-basis-law-p
    real-carrier real-zero real-less
    point-carrier distance basis active)))

(defun-sk q137164-second-countable-p
    (real-carrier real-zero real-less
     point-carrier distance)
  (exists (basis active)
    (q137164-second-countable-witness-p
     real-carrier real-zero real-less
     point-carrier distance basis active)))

;; Sigma algebras, measures, and exact s-finiteness.

(defun-sk q137164-measurable-space-laws-p
    (point-carrier measurable)
  (forall (set left right complement family union)
    (and
     (implies
      (q137164-apply1 measurable set)
      (q137164-set-p point-carrier set))
     (implies
      (and
       (q137164-set-p point-carrier left)
       (q137164-set-p point-carrier right)
       (q137164-set-equivalent-p
        point-carrier left right))
      (iff
       (q137164-apply1 measurable left)
       (q137164-apply1 measurable right)))
     (implies
      (and
       (q137164-set-p point-carrier set)
       (q137164-empty-set-p point-carrier set))
      (q137164-apply1 measurable set))
     (implies
      (and
       (q137164-apply1 measurable set)
       (q137164-set-p point-carrier complement)
       (q137164-complement-of-p
        point-carrier set complement))
      (q137164-apply1 measurable complement))
     (implies
      (and
       (q137164-set-sequence-p point-carrier family)
       (q137164-family-measurable-p measurable family)
       (q137164-set-p point-carrier union)
       (q137164-union-of-family-p
        point-carrier family union))
      (q137164-apply1 measurable union)))))

(defun q137164-measurable-space-p
    (point-carrier measurable)
  (and
   (tamep-functionp point-carrier)
   (tamep-functionp measurable)
   (q137164-measurable-space-laws-p
    point-carrier measurable)))

(defun-sk q137164-opens-measurable-p
    (real-carrier real-zero real-less
     point-carrier distance measurable)
  (forall (set)
    (implies
     (q137164-metric-open-set-p
      real-carrier real-zero real-less
      point-carrier distance set)
     (q137164-apply1 measurable set))))

(defun q137164-ennreal-finite (value)
  (list :q137164-finite value))

(defun q137164-ennreal-top ()
  :q137164-top)

(defun q137164-ennreal-zero (real-zero)
  (q137164-ennreal-finite real-zero))

(defun q137164-ennreal-finite-p
    (real-carrier real-zero real-less value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :q137164-finite)
   (q137164-member-p real-carrier (cadr value))
   (q137164-real-leq
    real-less real-zero (cadr value))))

(defun q137164-ennreal-p
    (real-carrier real-zero real-less value)
  (or
   (equal value (q137164-ennreal-top))
   (q137164-ennreal-finite-p
    real-carrier real-zero real-less value)))

(defun q137164-ennreal-leq
    (real-less left right)
  (cond
   ((equal right (q137164-ennreal-top)) t)
   ((equal left (q137164-ennreal-top)) nil)
   (t
    (q137164-real-leq
     real-less (cadr left) (cadr right)))))

(defun q137164-ennreal-add
    (real-add left right)
  (if (or
       (equal left (q137164-ennreal-top))
       (equal right (q137164-ennreal-top)))
      (q137164-ennreal-top)
    (q137164-ennreal-finite
     (q137164-apply2
      real-add (cadr left) (cadr right)))))

(defun q137164-measure-partial-sum
    (real-zero real-add measure family count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q137164-ennreal-zero real-zero)
    (q137164-ennreal-add
     real-add
     (q137164-measure-partial-sum
      real-zero real-add measure family (1- count))
     (q137164-apply1
      measure (q137164-apply1 family (1- count))))))

(defun-sk q137164-measure-series-upper-bound-p
    (real-zero real-add real-less
     measure family bound)
  (forall (count)
    (implies
     (natp count)
     (q137164-ennreal-leq
      real-less
      (q137164-measure-partial-sum
       real-zero real-add measure family count)
      bound))))

(defun-sk q137164-measure-series-sum-p
    (real-carrier real-zero real-add real-less
     measure family total)
  (forall (bound)
    (and
     (q137164-ennreal-p
      real-carrier real-zero real-less total)
     (q137164-measure-series-upper-bound-p
      real-zero real-add real-less
      measure family total)
     (implies
      (and
       (q137164-ennreal-p
        real-carrier real-zero real-less bound)
       (q137164-measure-series-upper-bound-p
        real-zero real-add real-less
        measure family bound))
      (q137164-ennreal-leq
       real-less total bound)))))

(defun-sk q137164-measure-laws-p
    (real-carrier real-zero real-add real-less
     point-carrier measurable measure)
  (forall (set left right family union)
    (and
     (implies
      (q137164-set-p point-carrier set)
      (q137164-ennreal-p
       real-carrier real-zero real-less
       (q137164-apply1 measure set)))
     (implies
      (and
       (q137164-set-p point-carrier left)
       (q137164-set-p point-carrier right)
       (q137164-set-equivalent-p
        point-carrier left right))
      (equal
       (q137164-apply1 measure left)
       (q137164-apply1 measure right)))
     (implies
      (and
       (q137164-set-p point-carrier set)
       (q137164-empty-set-p point-carrier set))
      (equal
       (q137164-apply1 measure set)
       (q137164-ennreal-zero real-zero)))
     (implies
      (and
       (q137164-set-sequence-p point-carrier family)
       (q137164-family-measurable-p measurable family)
       (q137164-family-pairwise-disjoint-p
        point-carrier family)
       (q137164-set-p point-carrier union)
       (q137164-union-of-family-p
        point-carrier family union))
      (q137164-measure-series-sum-p
       real-carrier real-zero real-add real-less
       measure family
       (q137164-apply1 measure union))))))

(defun q137164-measure-space-p
    (real-carrier real-zero real-add real-less
     point-carrier measurable measure)
  (and
   (q137164-measurable-space-p
    point-carrier measurable)
   (tamep-functionp measure)
   (q137164-measure-laws-p
    real-carrier real-zero real-add real-less
    point-carrier measurable measure)))

(defun q137164-finite-measure-p
    (point-carrier measure)
  (not
   (equal
    (q137164-apply1 measure point-carrier)
    (q137164-ennreal-top))))

(defun-sk q137164-component-measures-p
    (real-carrier real-zero real-add real-less
     point-carrier measurable components)
  (forall (n)
    (implies
     (natp n)
     (let ((component (q137164-apply1 components n)))
       (and
        (tamep-functionp component)
        (q137164-measure-space-p
         real-carrier real-zero real-add real-less
         point-carrier measurable component)
        (q137164-finite-measure-p
         point-carrier component))))))

(defun q137164-component-partial-sum
    (real-zero real-add components set count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q137164-ennreal-zero real-zero)
    (q137164-ennreal-add
     real-add
     (q137164-component-partial-sum
      real-zero real-add components set (1- count))
     (q137164-apply1
      (q137164-apply1 components (1- count))
      set))))

(defun-sk q137164-component-series-upper-bound-p
    (real-zero real-add real-less
     components set bound)
  (forall (count)
    (implies
     (natp count)
     (q137164-ennreal-leq
      real-less
      (q137164-component-partial-sum
       real-zero real-add components set count)
      bound))))

(defun-sk q137164-component-series-sum-p
    (real-carrier real-zero real-add real-less
     components set total)
  (forall (bound)
    (and
     (q137164-ennreal-p
      real-carrier real-zero real-less total)
     (q137164-component-series-upper-bound-p
      real-zero real-add real-less
      components set total)
     (implies
      (and
       (q137164-ennreal-p
        real-carrier real-zero real-less bound)
       (q137164-component-series-upper-bound-p
        real-zero real-add real-less
        components set bound))
      (q137164-ennreal-leq
       real-less total bound)))))

(defun-sk q137164-component-sum-equals-measure-p
    (real-carrier real-zero real-add real-less
     point-carrier components measure)
  (forall (set)
    (implies
     (q137164-set-p point-carrier set)
     (q137164-component-series-sum-p
      real-carrier real-zero real-add real-less
      components set (q137164-apply1 measure set)))))

(defun q137164-sfinite-witness-p
    (real-carrier real-zero real-add real-less
     point-carrier measurable measure components)
  (and
   (tamep-functionp components)
   (q137164-component-measures-p
    real-carrier real-zero real-add real-less
    point-carrier measurable components)
   (q137164-component-sum-equals-measure-p
    real-carrier real-zero real-add real-less
    point-carrier components measure)))

(defun-sk q137164-sfinite-measure-p
    (real-carrier real-zero real-add real-less
     point-carrier measurable measure)
  (exists (components)
    (and
     (q137164-measure-space-p
      real-carrier real-zero real-add real-less
      point-carrier measurable measure)
     (q137164-sfinite-witness-p
      real-carrier real-zero real-add real-less
      point-carrier measurable measure components))))

;; The exact no-satellite-configuration definition of the Besicovitch
;; covering property.

(defun q137164-fin-index-p (index size)
  (and
   (natp index)
   (< index size)))

(defun-sk q137164-satellite-laws-p
    (real-carrier real-zero real-add real-multiply real-less
     point-carrier distance size tau centers radii)
  (forall (i j)
    (let ((ri (q137164-apply1 radii i))
          (rj (q137164-apply1 radii j))
          (ci (q137164-apply1 centers i))
          (cj (q137164-apply1 centers j))
          (last-center (q137164-apply1 centers size))
          (last-radius (q137164-apply1 radii size)))
      (and
       (implies
        (q137164-fin-index-p i (+ 1 size))
        (and
         (q137164-member-p point-carrier ci)
         (q137164-member-p real-carrier ri)
         (q137164-apply2 real-less real-zero ri)))
       (implies
        (and
         (q137164-fin-index-p i (+ 1 size))
         (q137164-fin-index-p j (+ 1 size))
         (not (equal i j)))
        (or
         (and
          (q137164-real-leq
           real-less ri
           (q137164-apply2 distance ci cj))
          (q137164-real-leq
           real-less rj
           (q137164-apply2 real-multiply tau ri)))
         (and
          (q137164-real-leq
           real-less rj
           (q137164-apply2 distance cj ci))
          (q137164-real-leq
           real-less ri
           (q137164-apply2 real-multiply tau rj)))))
       (implies
        (q137164-fin-index-p i size)
        (and
         (q137164-real-leq
          real-less ri
          (q137164-apply2 distance ci last-center))
         (q137164-real-leq
          real-less last-radius
          (q137164-apply2 real-multiply tau ri))
         (q137164-real-leq
          real-less
          (q137164-apply2 distance ci last-center)
          (q137164-apply2 real-add ri last-radius))))))))

(defun q137164-satellite-config-p
    (real-carrier real-zero real-add real-multiply real-less
     point-carrier distance size tau centers radii)
  (and
   (natp size)
   (q137164-member-p real-carrier tau)
   (tamep-functionp centers)
   (tamep-functionp radii)
   (q137164-satellite-laws-p
    real-carrier real-zero real-add real-multiply real-less
    point-carrier distance size tau centers radii)))

(defun-sk q137164-no-satellite-config-p
    (real-carrier real-zero real-add real-multiply real-less
     point-carrier distance size tau)
  (forall (centers radii)
    (not
     (q137164-satellite-config-p
      real-carrier real-zero real-add real-multiply real-less
      point-carrier distance size tau centers radii))))

(defun-sk q137164-has-besicovitch-covering-p
    (real-carrier real-zero real-one
     real-add real-multiply real-less
     point-carrier distance)
  (exists (size tau)
    (and
     (natp size)
     (q137164-member-p real-carrier tau)
     (q137164-apply2 real-less real-one tau)
     (q137164-no-satellite-config-p
      real-carrier real-zero real-add real-multiply real-less
      point-carrier distance size tau))))

;; Source hypotheses on admissible radii.

(defun-sk q137164-radius-family-values-p
    (real-carrier point-carrier admissible)
  (forall (x radius)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-apply2 admissible x radius))
     (q137164-member-p real-carrier radius))))

(defun q137164-radius-family-p
    (real-carrier point-carrier admissible)
  (and
   (tamep-functionp admissible)
   (q137164-radius-family-values-p
    real-carrier point-carrier admissible)))

(defun-sk q137164-admissible-radius-exists-p
    (real-carrier real-zero real-less
     admissible x delta)
  (exists (radius)
    (and
     (q137164-member-p real-carrier radius)
     (q137164-apply2 admissible x radius)
     (q137164-apply2 real-less real-zero radius)
     (q137164-apply2 real-less radius delta))))

(defun-sk q137164-admissible-arbitrarily-small-p
    (real-carrier real-zero real-less
     point-carrier admissible set)
  (forall (x delta)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-apply1 set x)
      (q137164-member-p real-carrier delta)
      (q137164-apply2 real-less real-zero delta))
     (q137164-admissible-radius-exists-p
      real-carrier real-zero real-less
      admissible x delta))))

(defun-sk q137164-positive-bound-p
    (real-zero real-less point-carrier set bound)
  (forall (x)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-apply1 set x))
     (q137164-apply2
      real-less real-zero (q137164-apply1 bound x)))))

;; The countable, subordinate, admissible, disjoint, almost-everywhere
;; closed-ball covering in the conclusion.

(defun-sk q137164-countable-code-laws-p
    (point-carrier set code)
  (forall (x y)
    (and
     (implies
      (and
       (q137164-member-p point-carrier x)
       (q137164-apply1 set x))
      (natp (q137164-apply1 code x)))
     (implies
      (and
       (q137164-member-p point-carrier x)
       (q137164-member-p point-carrier y)
       (q137164-apply1 set x)
       (q137164-apply1 set y)
       (equal
        (q137164-apply1 code x)
        (q137164-apply1 code y)))
      (equal x y)))))

(defun-sk q137164-countable-set-p
    (point-carrier set)
  (exists (code)
    (and
     (q137164-set-p point-carrier set)
     (tamep-functionp code)
     (q137164-countable-code-laws-p
      point-carrier set code))))

(defun-sk q137164-selected-radii-p
    (real-zero real-less
     point-carrier admissible bound centers radii)
  (forall (x)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-apply1 centers x))
     (let ((radius (q137164-apply1 radii x)))
       (and
        (q137164-apply2 admissible x radius)
        (q137164-apply2 real-less real-zero radius)
        (q137164-apply2
         real-less radius (q137164-apply1 bound x)))))))

(defun-sk q137164-covering-center-exists-p
    (real-less point-carrier distance centers radii point)
  (exists (center)
    (and
     (q137164-member-p point-carrier center)
     (q137164-apply1 centers center)
     (q137164-real-leq
      real-less
      (q137164-apply2 distance point center)
      (q137164-apply1 radii center)))))

(defun-sk q137164-uncovered-set-characterization-p
    (real-less point-carrier distance
     source-set centers radii uncovered)
  (forall (x)
    (implies
     (q137164-member-p point-carrier x)
     (iff
      (q137164-apply1 uncovered x)
      (and
       (q137164-apply1 source-set x)
       (not
        (q137164-covering-center-exists-p
         real-less point-carrier distance
         centers radii x)))))))

(defun q137164-uncovered-set-p
    (real-less point-carrier distance
     source-set centers radii uncovered)
  (and
   (q137164-set-p point-carrier uncovered)
   (q137164-uncovered-set-characterization-p
    real-less point-carrier distance
    source-set centers radii uncovered)))

(defun-sk q137164-null-set-p
    (real-zero point-carrier measurable measure set)
  (exists (measurable-cover)
    (and
     (q137164-set-p point-carrier measurable-cover)
     (q137164-apply1 measurable measurable-cover)
     (q137164-subset-p
      point-carrier set measurable-cover)
     (equal
      (q137164-apply1 measure measurable-cover)
      (q137164-ennreal-zero real-zero)))))

(defun-sk q137164-pairwise-disjoint-closed-balls-p
    (real-less point-carrier distance centers radii)
  (forall (x y z)
    (implies
     (and
      (q137164-member-p point-carrier x)
      (q137164-member-p point-carrier y)
      (q137164-member-p point-carrier z)
      (q137164-apply1 centers x)
      (q137164-apply1 centers y)
      (not (equal x y)))
     (not
      (and
       (q137164-real-leq
        real-less
        (q137164-apply2 distance z x)
        (q137164-apply1 radii x))
       (q137164-real-leq
        real-less
        (q137164-apply2 distance z y)
        (q137164-apply1 radii y)))))))

(defun q137164-covering-data-p
    (real-carrier real-zero real-less
     point-carrier distance measurable measure
     admissible source-set bound
     centers radii uncovered)
  (and
   (q137164-countable-set-p
    point-carrier centers)
   (q137164-subset-p
    point-carrier centers source-set)
   (q137164-function-p
    point-carrier real-carrier radii)
   (q137164-selected-radii-p
    real-zero real-less
    point-carrier admissible bound centers radii)
   (q137164-uncovered-set-p
    real-less point-carrier distance
    source-set centers radii uncovered)
   (q137164-null-set-p
    real-zero point-carrier measurable measure uncovered)
   (q137164-pairwise-disjoint-closed-balls-p
    real-less point-carrier distance centers radii)))

(defun-sk q137164-covering-exists-p
    (real-carrier real-zero real-less
     point-carrier distance measurable measure
     admissible source-set bound)
  (exists (centers radii uncovered)
    (q137164-covering-data-p
     real-carrier real-zero real-less
     point-carrier distance measurable measure
     admissible source-set bound
     centers radii uncovered)))

(defun-sk thousand-theorems-q137164-besicovitch-covering-statement ()
  (forall
      (real-carrier real-zero real-one
       real-add real-multiply real-negate real-inverse real-less
       point-carrier distance measurable measure
       admissible source-set bound)
    (implies
     (and
      (q137164-real-field-p
       real-carrier real-zero real-one
       real-add real-multiply real-negate real-inverse real-less)
      (q137164-metric-space-p
       real-carrier real-zero real-add real-less
       point-carrier distance)
      (q137164-second-countable-p
       real-carrier real-zero real-less
       point-carrier distance)
      (q137164-measurable-space-p
       point-carrier measurable)
      (q137164-opens-measurable-p
       real-carrier real-zero real-less
       point-carrier distance measurable)
      (q137164-sfinite-measure-p
       real-carrier real-zero real-add real-less
       point-carrier measurable measure)
      (q137164-has-besicovitch-covering-p
       real-carrier real-zero real-one
       real-add real-multiply real-less
       point-carrier distance)
      (q137164-radius-family-p
       real-carrier point-carrier admissible)
      (q137164-set-p point-carrier source-set)
      (q137164-function-p
       point-carrier real-carrier bound)
      (q137164-admissible-arbitrarily-small-p
       real-carrier real-zero real-less
       point-carrier admissible source-set)
      (q137164-positive-bound-p
       real-zero real-less point-carrier source-set bound))
     (q137164-covering-exists-p
      real-carrier real-zero real-less
      point-carrier distance measurable measure
      admissible source-set bound))))

(value-triple :itpeval-statement-checked)
:q
