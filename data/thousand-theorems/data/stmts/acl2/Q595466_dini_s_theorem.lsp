;; Statement-only formalization of thousand-theorems corpus artifact Q595466,
;; "Dini's theorem": a monotone net of continuous functions from an arbitrary
;; topological space to a solid-normed lattice ordered additive commutative
;; group converges locally uniformly when it converges pointwise to a
;; continuous limit. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The DEFSTUB evaluators present arbitrary carriers, operations, neighborhood
;; bases, and functions without restricting them to finite tables or tame
;; function syntax. Every law used by the source typeclasses is an explicit
;; hypothesis of the final statement predicate.

(defstub q595466-member-p (carrier object) t)
(defstub q595466-index-le-p (order left right) t)
(defstub q595466-add-value (addition left right) t)
(defstub q595466-neg-value (negation value) t)
(defstub q595466-group-le-p (order left right) t)
(defstub q595466-meet-value (meet left right) t)
(defstub q595466-join-value (join left right) t)
(defstub q595466-norm-lt-p (norm value rational-bound) t)
(defstub q595466-basis-at-p (basis point neighborhood) t)
(defstub q595466-neighborhood-member-p (basis neighborhood point) t)
(defstub q595466-family-value (family index point) t)
(defstub q595466-limit-value (limit point) t)

(defun q595466-positive-rational-p (value)
  (and (rationalp value) (< 0 value)))

;; The arbitrary index type is a preorder. It may be empty or non-directed.

(defun-sk q595466-preorder-laws-p (carrier order)
  (forall (left middle right)
    (and
     (implies
      (q595466-member-p carrier left)
      (q595466-index-le-p order left left))
     (implies
      (and
       (q595466-member-p carrier left)
       (q595466-member-p carrier middle)
       (q595466-member-p carrier right)
       (q595466-index-le-p order left middle)
       (q595466-index-le-p order middle right))
      (q595466-index-le-p order left right)))))

;; A neighborhood basis presents exactly the topology needed by continuity
;; and local uniform convergence. The basis axioms are equivalent to the usual
;; neighborhood-system axioms and do not impose separation or compactness.

(defun-sk q595466-basis-subset-p
    (domain basis smaller larger)
  (forall (point)
    (implies
     (and
      (q595466-member-p domain point)
      (q595466-neighborhood-member-p basis smaller point))
     (q595466-neighborhood-member-p basis larger point))))

(defun-sk q595466-basis-neighborhood-exists-p
    (domain basis point)
  (exists (neighborhood)
    (q595466-basis-at-p basis point neighborhood)))

(defun-sk q595466-basis-validity-laws-p
    (domain basis)
  (forall (point neighborhood member)
    (and
     (implies
      (q595466-member-p domain point)
      (q595466-basis-neighborhood-exists-p
       domain basis point))
     (implies
      (q595466-basis-at-p basis point neighborhood)
      (and
       (q595466-member-p domain point)
       (q595466-neighborhood-member-p
        basis neighborhood point)
       (implies
        (q595466-neighborhood-member-p
         basis neighborhood member)
        (q595466-member-p domain member)))))))

(defun q595466-common-refinement-p
    (domain basis point left right refinement)
  (and
   (q595466-basis-at-p basis point refinement)
   (q595466-basis-subset-p
    domain basis refinement left)
   (q595466-basis-subset-p
    domain basis refinement right)))

(defun-sk q595466-common-refinement-exists-p
    (domain basis point left right)
  (exists (refinement)
    (q595466-common-refinement-p
     domain basis point left right refinement)))

(defun-sk q595466-basis-directed-laws-p
    (domain basis)
  (forall (point left right)
    (implies
     (and
      (q595466-member-p domain point)
      (q595466-basis-at-p basis point left)
      (q595466-basis-at-p basis point right))
     (q595466-common-refinement-exists-p
      domain basis point left right))))

(defun-sk q595466-local-refinement-at-point-exists-p
    (domain basis larger point)
  (exists (refinement)
    (and
     (q595466-basis-at-p basis point refinement)
     (q595466-basis-subset-p
      domain basis refinement larger))))

(defun-sk q595466-locality-neighborhood-p
    (domain basis point larger neighborhood)
  (forall (member)
    (and
     (q595466-basis-at-p basis point neighborhood)
     (implies
      (and
       (q595466-member-p domain member)
       (q595466-neighborhood-member-p
        basis neighborhood member))
      (q595466-local-refinement-at-point-exists-p
       domain basis larger member)))))

(defun-sk q595466-locality-neighborhood-exists-p
    (domain basis point larger)
  (exists (neighborhood)
    (q595466-locality-neighborhood-p
     domain basis point larger neighborhood)))

(defun-sk q595466-basis-locality-laws-p
    (domain basis)
  (forall (point neighborhood)
    (implies
     (and
      (q595466-member-p domain point)
      (q595466-basis-at-p basis point neighborhood))
     (q595466-locality-neighborhood-exists-p
      domain basis point neighborhood))))

(defun q595466-topological-basis-p (domain basis)
  (and
   (q595466-basis-validity-laws-p domain basis)
   (q595466-basis-directed-laws-p domain basis)
   (q595466-basis-locality-laws-p domain basis)))

;; Additive commutative group and lattice-order laws for the codomain.

(defun-sk q595466-add-comm-group-laws-p
    (carrier zero addition negation)
  (forall (left middle right)
    (and
     (q595466-member-p carrier zero)
     (implies
      (and
       (q595466-member-p carrier left)
       (q595466-member-p carrier middle)
       (q595466-member-p carrier right))
      (let ((left-middle
             (q595466-add-value addition left middle))
            (middle-right
             (q595466-add-value addition middle right))
            (negative-left
             (q595466-neg-value negation left)))
        (and
         (q595466-member-p carrier left-middle)
         (q595466-member-p carrier negative-left)
         (equal
          (q595466-add-value
           addition left-middle right)
          (q595466-add-value
           addition left middle-right))
         (equal
          left-middle
          (q595466-add-value addition middle left))
         (equal
          (q595466-add-value addition left zero)
          left)
         (equal
          (q595466-add-value
           addition left negative-left)
          zero)))))))

(defun-sk q595466-lattice-order-laws-p
    (carrier order meet join)
  (forall (left middle right)
    (and
     (implies
      (q595466-member-p carrier left)
      (q595466-group-le-p order left left))
     (implies
      (and
       (q595466-member-p carrier left)
       (q595466-member-p carrier middle)
       (q595466-group-le-p order left middle)
       (q595466-group-le-p order middle left))
      (equal left middle))
     (implies
      (and
       (q595466-member-p carrier left)
       (q595466-member-p carrier middle)
       (q595466-member-p carrier right)
       (q595466-group-le-p order left middle)
       (q595466-group-le-p order middle right))
      (q595466-group-le-p order left right))
     (implies
      (and
       (q595466-member-p carrier left)
       (q595466-member-p carrier middle)
       (q595466-member-p carrier right))
      (let ((infimum
             (q595466-meet-value meet left middle))
            (supremum
             (q595466-join-value join left middle)))
        (and
         (q595466-member-p carrier infimum)
         (q595466-member-p carrier supremum)
         (q595466-group-le-p order infimum left)
         (q595466-group-le-p order infimum middle)
         (implies
          (and
           (q595466-group-le-p order right left)
           (q595466-group-le-p order right middle))
          (q595466-group-le-p
           order right infimum))
         (q595466-group-le-p order left supremum)
         (q595466-group-le-p order middle supremum)
         (implies
          (and
           (q595466-group-le-p order left right)
           (q595466-group-le-p order middle right))
          (q595466-group-le-p
           order supremum right))))))))

(defun-sk q595466-ordered-addition-laws-p
    (carrier addition order)
  (forall (left right shift)
    (implies
     (and
      (q595466-member-p carrier left)
      (q595466-member-p carrier right)
      (q595466-member-p carrier shift)
      (q595466-group-le-p order left right))
     (q595466-group-le-p
      order
      (q595466-add-value addition left shift)
      (q595466-add-value addition right shift)))))

;; Rational upper cuts represent arbitrary finite nonnegative real norm
;; values. Roundedness, upward closure, and finiteness make this equivalent to
;; a real-valued norm without restricting norm values to rational numbers.

(defun-sk q595466-norm-rounded-witness-exists-p
    (norm value bound)
  (exists (smaller)
    (and
     (q595466-positive-rational-p smaller)
     (< smaller bound)
     (q595466-norm-lt-p norm value smaller))))

(defun-sk q595466-norm-finite-bound-exists-p
    (norm value)
  (exists (bound)
    (and
     (q595466-positive-rational-p bound)
     (q595466-norm-lt-p norm value bound))))

(defun-sk q595466-norm-cut-laws-p
    (carrier norm)
  (forall (value lower upper)
    (implies
     (q595466-member-p carrier value)
     (and
      (q595466-norm-finite-bound-exists-p
       norm value)
      (implies
       (and
        (q595466-positive-rational-p lower)
        (q595466-positive-rational-p upper)
        (< lower upper)
        (q595466-norm-lt-p norm value lower))
       (q595466-norm-lt-p norm value upper))
      (implies
       (and
        (q595466-positive-rational-p upper)
        (q595466-norm-lt-p norm value upper))
       (q595466-norm-rounded-witness-exists-p
        norm value upper))))))

(defun-sk q595466-norm-zero-p (norm value)
  (forall (bound)
    (implies
     (q595466-positive-rational-p bound)
     (q595466-norm-lt-p norm value bound))))

(defun-sk q595466-norm-equal-p (norm left right)
  (forall (bound)
    (implies
     (q595466-positive-rational-p bound)
     (iff
      (q595466-norm-lt-p norm left bound)
      (q595466-norm-lt-p norm right bound)))))

(defun-sk q595466-norm-le-p (norm left right)
  (forall (bound)
    (implies
     (and
      (q595466-positive-rational-p bound)
      (q595466-norm-lt-p norm right bound))
     (q595466-norm-lt-p norm left bound))))

(defun-sk q595466-normed-group-laws-p
    (carrier zero addition negation norm)
  (forall (left right left-bound right-bound)
    (and
     (q595466-norm-cut-laws-p carrier norm)
     (implies
      (and
       (q595466-member-p carrier left)
       (q595466-member-p carrier right))
      (and
       (iff
        (equal left zero)
        (q595466-norm-zero-p norm left))
       (q595466-norm-equal-p
        norm
        (q595466-neg-value negation left)
        left)
       (implies
        (and
         (q595466-positive-rational-p left-bound)
         (q595466-positive-rational-p right-bound)
         (q595466-norm-lt-p
          norm left left-bound)
         (q595466-norm-lt-p
          norm right right-bound))
        (q595466-norm-lt-p
         norm
         (q595466-add-value addition left right)
         (+ left-bound right-bound))))))))

(defun q595466-absolute-value
    (join negation value)
  (q595466-join-value
   join value (q595466-neg-value negation value)))

(defun-sk q595466-solid-norm-laws-p
    (carrier order join negation norm)
  (forall (left right)
    (implies
     (and
      (q595466-member-p carrier left)
      (q595466-member-p carrier right)
      (q595466-group-le-p
       order
       (q595466-absolute-value
        join negation left)
       (q595466-absolute-value
        join negation right)))
     (q595466-norm-le-p norm left right))))

(defun q595466-codomain-structure-p
    (carrier zero addition negation order meet join norm)
  (and
   (q595466-add-comm-group-laws-p
    carrier zero addition negation)
   (q595466-lattice-order-laws-p
    carrier order meet join)
   (q595466-ordered-addition-laws-p
    carrier addition order)
   (q595466-normed-group-laws-p
    carrier zero addition negation norm)
   (q595466-solid-norm-laws-p
    carrier order join negation norm)))

;; Typing, continuity, and monotonicity of the arbitrary family and limit.

(defun-sk q595466-family-values-p
    (index-carrier domain codomain family)
  (forall (index point)
    (implies
     (and
      (q595466-member-p index-carrier index)
      (q595466-member-p domain point))
     (q595466-member-p
      codomain
      (q595466-family-value family index point)))))

(defun-sk q595466-limit-values-p
    (domain codomain limit)
  (forall (point)
    (implies
     (q595466-member-p domain point)
     (q595466-member-p
      codomain
      (q595466-limit-value limit point)))))

(defun q595466-distance-lt-p
    (addition negation norm left right bound)
  (q595466-norm-lt-p
   norm
   (q595466-add-value
    addition left
    (q595466-neg-value negation right))
   bound))

(defun-sk q595466-family-continuity-neighborhood-p
    (domain basis addition negation norm
     family index point bound neighborhood)
  (forall (nearby)
    (and
     (q595466-basis-at-p basis point neighborhood)
     (implies
      (and
       (q595466-member-p domain nearby)
       (q595466-neighborhood-member-p
        basis neighborhood nearby))
      (q595466-distance-lt-p
       addition negation norm
       (q595466-family-value
        family index nearby)
       (q595466-family-value
        family index point)
       bound)))))

(defun-sk q595466-family-continuity-neighborhood-exists-p
    (domain basis addition negation norm
     family index point bound)
  (exists (neighborhood)
    (q595466-family-continuity-neighborhood-p
     domain basis addition negation norm
     family index point bound neighborhood)))

(defun-sk q595466-family-continuous-p
    (index-carrier domain basis addition negation norm family)
  (forall (index point bound)
    (implies
     (and
      (q595466-member-p index-carrier index)
      (q595466-member-p domain point)
      (q595466-positive-rational-p bound))
     (q595466-family-continuity-neighborhood-exists-p
      domain basis addition negation norm
      family index point bound))))

(defun-sk q595466-limit-continuity-neighborhood-p
    (domain basis addition negation norm
     limit point bound neighborhood)
  (forall (nearby)
    (and
     (q595466-basis-at-p basis point neighborhood)
     (implies
      (and
       (q595466-member-p domain nearby)
       (q595466-neighborhood-member-p
        basis neighborhood nearby))
      (q595466-distance-lt-p
       addition negation norm
       (q595466-limit-value limit nearby)
       (q595466-limit-value limit point)
       bound)))))

(defun-sk q595466-limit-continuity-neighborhood-exists-p
    (domain basis addition negation norm
     limit point bound)
  (exists (neighborhood)
    (q595466-limit-continuity-neighborhood-p
     domain basis addition negation norm
     limit point bound neighborhood)))

(defun-sk q595466-limit-continuous-p
    (domain basis addition negation norm limit)
  (forall (point bound)
    (implies
     (and
      (q595466-member-p domain point)
      (q595466-positive-rational-p bound))
     (q595466-limit-continuity-neighborhood-exists-p
      domain basis addition negation norm
      limit point bound))))

(defun-sk q595466-family-monotone-p
    (index-carrier index-order domain
     codomain-order family)
  (forall (left right point)
    (implies
     (and
      (q595466-member-p index-carrier left)
      (q595466-member-p index-carrier right)
      (q595466-member-p domain point)
      (q595466-index-le-p
       index-order left right))
     (q595466-group-le-p
      codomain-order
      (q595466-family-value family left point)
      (q595466-family-value family right point)))))

;; Membership in an atTop-event is represented by a finite intersection of
;; principal upper sets. This is exact for an arbitrary preorder and retains
;; the bottom-filter cases caused by empty carriers or incompatible bounds.

(defun q595466-index-bound-list-p
    (bounds index-carrier)
  (if (consp bounds)
      (and
       (q595466-member-p index-carrier (car bounds))
       (q595466-index-bound-list-p
        (cdr bounds) index-carrier))
    (equal bounds nil)))

(defun q595466-above-all-bounds-p
    (index-order bounds index)
  (if (consp bounds)
      (and
       (q595466-index-le-p
        index-order (car bounds) index)
       (q595466-above-all-bounds-p
        index-order (cdr bounds) index))
    (equal bounds nil)))

(defun-sk q595466-pointwise-tail-p
    (index-carrier index-order
     addition negation norm family limit
     point bound bounds)
  (forall (index)
    (implies
     (and
      (q595466-member-p index-carrier index)
      (q595466-above-all-bounds-p
       index-order bounds index))
     (q595466-distance-lt-p
      addition negation norm
      (q595466-family-value family index point)
      (q595466-limit-value limit point)
      bound))))

(defun-sk q595466-pointwise-eventually-p
    (index-carrier index-order
     addition negation norm family limit
     point bound)
  (exists (bounds)
    (and
     (q595466-index-bound-list-p
      bounds index-carrier)
     (q595466-pointwise-tail-p
      index-carrier index-order
      addition negation norm family limit
      point bound bounds))))

(defun-sk q595466-pointwise-tendsto-p
    (index-carrier index-order domain
     addition negation norm family limit)
  (forall (point bound)
    (implies
     (and
      (q595466-member-p domain point)
      (q595466-positive-rational-p bound))
     (q595466-pointwise-eventually-p
      index-carrier index-order
      addition negation norm family limit
      point bound))))

(defun-sk q595466-locally-uniform-tail-p
    (index-carrier index-order domain basis
     addition negation norm family limit
     neighborhood bound bounds)
  (forall (index nearby)
    (implies
     (and
      (q595466-member-p index-carrier index)
      (q595466-above-all-bounds-p
       index-order bounds index)
      (q595466-member-p domain nearby)
      (q595466-neighborhood-member-p
       basis neighborhood nearby))
     (q595466-distance-lt-p
      addition negation norm
      (q595466-family-value family index nearby)
      (q595466-limit-value limit nearby)
      bound))))

(defun-sk q595466-locally-uniform-witnesses-exist-p
    (index-carrier index-order domain basis
     addition negation norm family limit
     point bound)
  (exists (neighborhood bounds)
    (and
     (q595466-basis-at-p
      basis point neighborhood)
     (q595466-index-bound-list-p
      bounds index-carrier)
     (q595466-locally-uniform-tail-p
      index-carrier index-order domain basis
      addition negation norm family limit
      neighborhood bound bounds))))

(defun-sk q595466-tendsto-locally-uniformly-p
    (index-carrier index-order domain basis
     addition negation norm family limit)
  (forall (point bound)
    (implies
     (and
      (q595466-member-p domain point)
      (q595466-positive-rational-p bound))
     (q595466-locally-uniform-witnesses-exist-p
      index-carrier index-order domain basis
      addition negation norm family limit
      point bound))))

(defun thousand-theorems-q595466-dini-s-theorem-statement
    (index-carrier index-order
     domain neighborhood-basis
     codomain zero addition negation codomain-order meet join norm
     family limit)
  (implies
   (and
    (q595466-preorder-laws-p
     index-carrier index-order)
    (q595466-topological-basis-p
     domain neighborhood-basis)
    (q595466-codomain-structure-p
     codomain zero addition negation
     codomain-order meet join norm)
    (q595466-family-values-p
     index-carrier domain codomain family)
    (q595466-limit-values-p
     domain codomain limit)
    (q595466-family-continuous-p
     index-carrier domain neighborhood-basis
     addition negation norm family)
    (q595466-family-monotone-p
     index-carrier index-order domain
     codomain-order family)
    (q595466-limit-continuous-p
     domain neighborhood-basis
     addition negation norm limit)
    (q595466-pointwise-tendsto-p
     index-carrier index-order domain
     addition negation norm family limit))
   (q595466-tendsto-locally-uniformly-p
    index-carrier index-order domain neighborhood-basis
    addition negation norm family limit)))

(value-triple :itpeval-statement-checked)
:q
