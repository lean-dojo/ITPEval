;; Statement-only formalization of thousand-theorems corpus artifact Q1477053,
;; "Arzelà–Ascoli theorem": the closure of a pointwise equicontinuous family
;; of bounded continuous maps from a compact space, with range in a compact
;; subset of a metric space, is compact for uniform convergence. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, sets, families, and maps are ACL2 objects interpreted
;; by conservative application interfaces. Distances are represented exactly
;; by rounded rational upper cuts: DISTANCE-LT(x,y,q) means d(x,y) < q.
;; Thus metric values remain arbitrary finite nonnegative reals. DEFUN-SK
;; keeps all points, sets, covers, functions, radii, and finite subcovers in
;; their source quantifier scopes.

(defstub q1477053-member-p (collection object) t)

(defstub q1477053-value (function object) t)

(defstub q1477053-distance-lt-p (distance left right radius) t)

(defun q1477053-positive-rational-p (value)
  (and (rationalp value)
       (< 0 value)))

;; Extensional subsets and arbitrary families of subsets.

(defun-sk q1477053-set-contained-p (carrier set)
  (forall (x)
    (implies
     (q1477053-member-p set x)
     (q1477053-member-p carrier x))))

(defun q1477053-valid-set-p (carrier set)
  (q1477053-set-contained-p carrier set))

(defun-sk q1477053-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q1477053-member-p carrier x)
     (iff
      (q1477053-member-p left x)
      (q1477053-member-p right x)))))

(defun-sk q1477053-family-extensional-p (carrier family)
  (forall (left right)
    (implies
     (and
      (q1477053-valid-set-p carrier left)
      (q1477053-valid-set-p carrier right)
      (q1477053-set-equiv-p carrier left right))
     (iff
      (q1477053-member-p family left)
      (q1477053-member-p family right)))))

(defun-sk q1477053-family-members-valid-p (carrier family)
  (forall (set)
    (implies
     (q1477053-member-p family set)
     (q1477053-valid-set-p carrier set))))

(defun q1477053-family-of-sets-p (carrier family)
  (and
   (q1477053-family-extensional-p carrier family)
   (q1477053-family-members-valid-p carrier family)))

;; A general topology on the source carrier.

(defun q1477053-open-set-p (carrier topology set)
  (and
   (q1477053-valid-set-p carrier set)
   (q1477053-member-p topology set)))

(defun-sk q1477053-family-members-open-p
    (carrier topology family)
  (forall (set)
    (implies
     (q1477053-member-p family set)
     (q1477053-open-set-p carrier topology set))))

(defun-sk q1477053-empty-representation-p (carrier set)
  (forall (x)
    (implies
     (q1477053-member-p carrier x)
     (not (q1477053-member-p set x)))))

(defun-sk q1477053-full-representation-p (carrier set)
  (forall (x)
    (implies
     (q1477053-member-p carrier x)
     (q1477053-member-p set x))))

(defun-sk q1477053-intersection-representation-p
    (carrier left right intersection)
  (forall (x)
    (implies
     (q1477053-member-p carrier x)
     (iff
      (q1477053-member-p intersection x)
      (and
       (q1477053-member-p left x)
       (q1477053-member-p right x))))))

(defun-sk q1477053-union-member-p (carrier family x)
  (exists (set)
    (and
     (q1477053-valid-set-p carrier set)
     (q1477053-member-p family set)
     (q1477053-member-p set x))))

(defun-sk q1477053-union-representation-p
    (carrier family union)
  (forall (x)
    (implies
     (q1477053-member-p carrier x)
     (iff
      (q1477053-member-p union x)
      (q1477053-union-member-p carrier family x)))))

(defun-sk q1477053-empty-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q1477053-valid-set-p carrier set)
     (q1477053-empty-representation-p carrier set)
     (q1477053-open-set-p carrier topology set))))

(defun-sk q1477053-full-open-exists-p (carrier topology)
  (exists (set)
    (and
     (q1477053-valid-set-p carrier set)
     (q1477053-full-representation-p carrier set)
     (q1477053-open-set-p carrier topology set))))

(defun-sk q1477053-intersection-open-exists-p
    (carrier topology left right)
  (exists (intersection)
    (and
     (q1477053-valid-set-p carrier intersection)
     (q1477053-intersection-representation-p
      carrier left right intersection)
     (q1477053-open-set-p
      carrier topology intersection))))

(defun-sk q1477053-union-open-exists-p
    (carrier topology family)
  (exists (union)
    (and
     (q1477053-valid-set-p carrier union)
     (q1477053-union-representation-p
      carrier family union)
     (q1477053-open-set-p carrier topology union))))

(defun-sk q1477053-topology-closure-laws-p
    (carrier topology)
  (forall (left right family)
    (and
     (implies
      (and
       (q1477053-open-set-p carrier topology left)
       (q1477053-open-set-p carrier topology right))
      (q1477053-intersection-open-exists-p
       carrier topology left right))
     (implies
      (and
       (q1477053-family-of-sets-p carrier family)
       (q1477053-family-members-open-p
        carrier topology family))
      (q1477053-union-open-exists-p
       carrier topology family)))))

(defun q1477053-topological-space-p (carrier topology)
  (and
   (q1477053-family-of-sets-p carrier topology)
   (q1477053-empty-open-exists-p carrier topology)
   (q1477053-full-open-exists-p carrier topology)
   (q1477053-topology-closure-laws-p carrier topology)))

;; Compactness in an arbitrary topology, by unrestricted open covers.

(defun-sk q1477053-cover-point-p (carrier family x)
  (exists (set)
    (and
     (q1477053-valid-set-p carrier set)
     (q1477053-member-p family set)
     (q1477053-member-p set x))))

(defun-sk q1477053-cover-p (carrier set family)
  (forall (x)
    (implies
     (and
      (q1477053-member-p carrier x)
      (q1477053-member-p set x))
     (q1477053-cover-point-p carrier family x))))

(defun q1477053-finite-subcover-elements-p
    (sets carrier family)
  (if (consp sets)
      (and
       (q1477053-valid-set-p carrier (car sets))
       (q1477053-member-p family (car sets))
       (q1477053-finite-subcover-elements-p
        (cdr sets) carrier family))
    (equal sets nil)))

(defun q1477053-finite-subcover-point-p (sets x)
  (if (consp sets)
      (or
       (q1477053-member-p (car sets) x)
       (q1477053-finite-subcover-point-p (cdr sets) x))
    nil))

(defun-sk q1477053-finite-subcover-covers-p
    (carrier set sets)
  (forall (x)
    (implies
     (and
      (q1477053-member-p carrier x)
      (q1477053-member-p set x))
     (q1477053-finite-subcover-point-p sets x))))

(defun q1477053-finite-subcover-p
    (sets carrier set family)
  (and
   (true-listp sets)
   (q1477053-finite-subcover-elements-p
    sets carrier family)
   (q1477053-finite-subcover-covers-p
    carrier set sets)))

(defun-sk q1477053-finite-subcover-exists-p
    (carrier set family)
  (exists (sets)
    (q1477053-finite-subcover-p
     sets carrier set family)))

(defun-sk q1477053-compact-cover-law-p
    (carrier topology set)
  (forall (family)
    (implies
     (and
      (q1477053-family-of-sets-p carrier family)
      (q1477053-family-members-open-p
       carrier topology family)
      (q1477053-cover-p carrier set family))
     (q1477053-finite-subcover-exists-p
      carrier set family))))

(defun q1477053-compact-set-p
    (carrier topology set)
  (and
   (q1477053-valid-set-p carrier set)
   (q1477053-compact-cover-law-p
    carrier topology set)))

;; Exact finite real-valued metrics via rounded rational upper cuts. The
;; separation clause is the ACL2 form of PseudoMetricSpace plus T2Space.

(defun-sk q1477053-distance-finite-p
    (distance left right)
  (exists (radius)
    (and
     (q1477053-positive-rational-p radius)
     (q1477053-distance-lt-p
      distance left right radius))))

(defun-sk q1477053-distance-rounded-p
    (distance left right radius)
  (exists (smaller)
    (and
     (q1477053-positive-rational-p smaller)
     (rationalp radius)
     (< smaller radius)
     (q1477053-distance-lt-p
      distance left right smaller))))

(defun-sk q1477053-positive-distance-p
    (distance left right)
  (exists (radius)
    (and
     (q1477053-positive-rational-p radius)
     (not
      (q1477053-distance-lt-p
       distance left right radius)))))

(defun-sk q1477053-metric-laws-p
    (carrier distance)
  (forall (x y z q r s)
    (implies
     (and
      (q1477053-member-p carrier x)
      (q1477053-member-p carrier y)
      (q1477053-member-p carrier z))
     (and
      (implies
       (q1477053-distance-lt-p distance x y q)
       (q1477053-positive-rational-p q))
      (implies
       (and
        (q1477053-distance-lt-p distance x y q)
        (rationalp r)
        (< q r))
       (q1477053-distance-lt-p distance x y r))
      (implies
       (q1477053-distance-lt-p distance x y q)
       (q1477053-distance-rounded-p
        distance x y q))
      (q1477053-distance-finite-p distance x y)
      (iff
       (q1477053-distance-lt-p distance x y q)
       (q1477053-distance-lt-p distance y x q))
      (iff
       (q1477053-distance-lt-p distance x x q)
       (q1477053-positive-rational-p q))
      (implies
       (not (equal x y))
       (q1477053-positive-distance-p distance x y))
      (implies
       (and
        (q1477053-positive-rational-p r)
        (q1477053-positive-rational-p s)
        (q1477053-distance-lt-p distance x y r)
        (q1477053-distance-lt-p distance y z s))
       (q1477053-distance-lt-p
        distance x z (+ r s)))))))

(defun q1477053-metric-space-p (carrier distance)
  (q1477053-metric-laws-p carrier distance))

;; The topology induced by the metric, and compact metric subsets.

(defun-sk q1477053-metric-ball-subset-p
    (carrier distance center radius set)
  (forall (point)
    (implies
     (and
      (q1477053-member-p carrier point)
      (q1477053-distance-lt-p
       distance center point radius))
     (q1477053-member-p set point))))

(defun-sk q1477053-metric-open-radius-exists-p
    (carrier distance set center)
  (exists (radius)
    (and
     (q1477053-positive-rational-p radius)
     (q1477053-metric-ball-subset-p
      carrier distance center radius set))))

(defun-sk q1477053-metric-open-law-p
    (carrier distance set)
  (forall (center)
    (implies
     (and
      (q1477053-member-p carrier center)
      (q1477053-member-p set center))
     (q1477053-metric-open-radius-exists-p
      carrier distance set center))))

(defun q1477053-metric-open-set-p
    (carrier distance set)
  (and
   (q1477053-valid-set-p carrier set)
   (q1477053-metric-open-law-p
    carrier distance set)))

(defun-sk q1477053-family-members-metric-open-p
    (carrier distance family)
  (forall (set)
    (implies
     (q1477053-member-p family set)
     (q1477053-metric-open-set-p
      carrier distance set))))

(defun-sk q1477053-metric-compact-cover-law-p
    (carrier distance set)
  (forall (family)
    (implies
     (and
      (q1477053-family-of-sets-p carrier family)
      (q1477053-family-members-metric-open-p
       carrier distance family)
      (q1477053-cover-p carrier set family))
     (q1477053-finite-subcover-exists-p
      carrier set family))))

(defun q1477053-metric-compact-set-p
    (carrier distance set)
  (and
   (q1477053-valid-set-p carrier set)
   (q1477053-metric-compact-cover-law-p
    carrier distance set)))

;; Continuous maps from the source topology to the metric codomain.

(defun-sk q1477053-map-into-p
    (source-carrier target-carrier mapping)
  (forall (x)
    (implies
     (q1477053-member-p source-carrier x)
     (q1477053-member-p
      target-carrier
      (q1477053-value mapping x)))))

(defun-sk q1477053-preimage-representation-p
    (source-carrier mapping target-set source-set)
  (forall (x)
    (implies
     (q1477053-member-p source-carrier x)
     (iff
      (q1477053-member-p source-set x)
      (q1477053-member-p
       target-set
       (q1477053-value mapping x))))))

(defun-sk q1477053-open-preimage-exists-p
    (source-carrier source-topology mapping target-set)
  (exists (source-set)
    (and
     (q1477053-valid-set-p source-carrier source-set)
     (q1477053-preimage-representation-p
      source-carrier mapping target-set source-set)
     (q1477053-open-set-p
      source-carrier source-topology source-set))))

(defun-sk q1477053-continuity-law-p
    (source-carrier source-topology
     target-carrier target-distance mapping)
  (forall (target-set)
    (implies
     (q1477053-metric-open-set-p
      target-carrier target-distance target-set)
     (q1477053-open-preimage-exists-p
      source-carrier source-topology
      mapping target-set))))

(defun q1477053-continuous-map-p
    (source-carrier source-topology
     target-carrier target-distance mapping)
  (and
   (q1477053-map-into-p
    source-carrier target-carrier mapping)
   (q1477053-continuity-law-p
    source-carrier source-topology
    target-carrier target-distance mapping)))

(defun-sk q1477053-map-equiv-p
    (source-carrier left right)
  (forall (x)
    (implies
     (q1477053-member-p source-carrier x)
     (equal
      (q1477053-value left x)
      (q1477053-value right x)))))

;; Sets of bounded continuous functions. On the compact source, every
;; continuous metric-valued map is bounded, so this is the same collection
;; of functions as the bundled type in the Lean source.

(defun-sk q1477053-function-set-contained-p
    (source-carrier source-topology
     target-carrier target-distance set)
  (forall (mapping)
    (implies
     (q1477053-member-p set mapping)
     (q1477053-continuous-map-p
      source-carrier source-topology
      target-carrier target-distance mapping))))

(defun-sk q1477053-function-set-extensional-p
    (source-carrier source-topology
     target-carrier target-distance set)
  (forall (left right)
    (implies
     (and
      (q1477053-continuous-map-p
       source-carrier source-topology
       target-carrier target-distance left)
      (q1477053-continuous-map-p
       source-carrier source-topology
       target-carrier target-distance right)
      (q1477053-map-equiv-p source-carrier left right))
     (iff
      (q1477053-member-p set left)
      (q1477053-member-p set right)))))

(defun q1477053-valid-function-set-p
    (source-carrier source-topology
     target-carrier target-distance set)
  (and
   (q1477053-function-set-contained-p
    source-carrier source-topology
    target-carrier target-distance set)
   (q1477053-function-set-extensional-p
    source-carrier source-topology
    target-carrier target-distance set)))

(defun-sk q1477053-function-set-equiv-p
    (source-carrier source-topology
     target-carrier target-distance left right)
  (forall (mapping)
    (implies
     (q1477053-continuous-map-p
      source-carrier source-topology
      target-carrier target-distance mapping)
     (iff
      (q1477053-member-p left mapping)
      (q1477053-member-p right mapping)))))

(defun-sk q1477053-function-family-extensional-p
    (source-carrier source-topology
     target-carrier target-distance family)
  (forall (left right)
    (implies
     (and
      (q1477053-valid-function-set-p
       source-carrier source-topology
       target-carrier target-distance left)
      (q1477053-valid-function-set-p
       source-carrier source-topology
       target-carrier target-distance right)
      (q1477053-function-set-equiv-p
       source-carrier source-topology
       target-carrier target-distance left right))
     (iff
      (q1477053-member-p family left)
      (q1477053-member-p family right)))))

(defun-sk q1477053-function-family-members-valid-p
    (source-carrier source-topology
     target-carrier target-distance family)
  (forall (set)
    (implies
     (q1477053-member-p family set)
     (q1477053-valid-function-set-p
      source-carrier source-topology
      target-carrier target-distance set))))

(defun q1477053-function-family-of-sets-p
    (source-carrier source-topology
     target-carrier target-distance family)
  (and
   (q1477053-function-family-extensional-p
    source-carrier source-topology
    target-carrier target-distance family)
   (q1477053-function-family-members-valid-p
    source-carrier source-topology
    target-carrier target-distance family)))

;; Pointwise equicontinuity and the common compact range.

(defun-sk q1477053-equicontinuity-neighborhood-law-p
    (source-carrier source-topology
     target-distance family center radius neighborhood)
  (forall (mapping point)
    (implies
     (and
      (q1477053-member-p family mapping)
      (q1477053-member-p source-carrier point)
      (q1477053-member-p neighborhood point))
     (q1477053-distance-lt-p
      target-distance
      (q1477053-value mapping point)
      (q1477053-value mapping center)
      radius))))

(defun-sk q1477053-equicontinuity-neighborhood-exists-p
    (source-carrier source-topology
     target-distance family center radius)
  (exists (neighborhood)
    (and
     (q1477053-open-set-p
      source-carrier source-topology neighborhood)
     (q1477053-member-p neighborhood center)
     (q1477053-equicontinuity-neighborhood-law-p
      source-carrier source-topology target-distance
      family center radius neighborhood))))

(defun-sk q1477053-equicontinuous-p
    (source-carrier source-topology target-distance family)
  (forall (center radius)
    (implies
     (and
      (q1477053-member-p source-carrier center)
      (q1477053-positive-rational-p radius))
     (q1477053-equicontinuity-neighborhood-exists-p
      source-carrier source-topology target-distance
      family center radius))))

(defun-sk q1477053-family-range-in-set-p
    (source-carrier family target-set)
  (forall (mapping x)
    (implies
     (and
      (q1477053-member-p family mapping)
      (q1477053-member-p source-carrier x))
     (q1477053-member-p
      target-set
      (q1477053-value mapping x)))))

;; Uniform convergence. The strict upper cut of the supremum distance is
;; expressed by a rational bound strictly below the requested radius.

(defun-sk q1477053-uniform-bound-p
    (source-carrier target-distance left right bound)
  (forall (x)
    (implies
     (q1477053-member-p source-carrier x)
     (q1477053-distance-lt-p
      target-distance
      (q1477053-value left x)
      (q1477053-value right x)
      bound))))

(defun-sk q1477053-uniform-distance-lt-p
    (source-carrier target-distance left right radius)
  (exists (bound)
    (and
     (q1477053-positive-rational-p bound)
     (rationalp radius)
     (< bound radius)
     (q1477053-uniform-bound-p
      source-carrier target-distance
      left right bound))))

(defun-sk q1477053-uniform-ball-subset-p
    (source-carrier source-topology
     target-carrier target-distance set center radius)
  (forall (mapping)
    (implies
     (and
      (q1477053-continuous-map-p
       source-carrier source-topology
       target-carrier target-distance mapping)
      (q1477053-uniform-distance-lt-p
       source-carrier target-distance
       center mapping radius))
     (q1477053-member-p set mapping))))

(defun-sk q1477053-uniform-open-radius-exists-p
    (source-carrier source-topology
     target-carrier target-distance set center)
  (exists (radius)
    (and
     (q1477053-positive-rational-p radius)
     (q1477053-uniform-ball-subset-p
      source-carrier source-topology
      target-carrier target-distance set center radius))))

(defun-sk q1477053-uniform-open-law-p
    (source-carrier source-topology
     target-carrier target-distance set)
  (forall (center)
    (implies
     (and
      (q1477053-continuous-map-p
       source-carrier source-topology
       target-carrier target-distance center)
      (q1477053-member-p set center))
     (q1477053-uniform-open-radius-exists-p
      source-carrier source-topology
      target-carrier target-distance set center))))

(defun q1477053-uniform-open-function-set-p
    (source-carrier source-topology
     target-carrier target-distance set)
  (and
   (q1477053-valid-function-set-p
    source-carrier source-topology
    target-carrier target-distance set)
   (q1477053-uniform-open-law-p
    source-carrier source-topology
    target-carrier target-distance set)))

(defun-sk q1477053-function-family-members-uniform-open-p
    (source-carrier source-topology
     target-carrier target-distance family)
  (forall (set)
    (implies
     (q1477053-member-p family set)
     (q1477053-uniform-open-function-set-p
      source-carrier source-topology
      target-carrier target-distance set))))

(defun-sk q1477053-closure-approximation-exists-p
    (source-carrier source-topology
     target-carrier target-distance family mapping radius)
  (exists (approximant)
    (and
     (q1477053-member-p family approximant)
     (q1477053-continuous-map-p
      source-carrier source-topology
      target-carrier target-distance approximant)
     (q1477053-uniform-distance-lt-p
      source-carrier target-distance
      mapping approximant radius))))

(defun-sk q1477053-uniform-closure-law-p
    (source-carrier source-topology
     target-carrier target-distance family mapping)
  (forall (radius)
    (implies
     (q1477053-positive-rational-p radius)
     (q1477053-closure-approximation-exists-p
      source-carrier source-topology
      target-carrier target-distance
      family mapping radius))))

(defun q1477053-in-uniform-closure-p
    (source-carrier source-topology
     target-carrier target-distance family mapping)
  (and
   (q1477053-continuous-map-p
    source-carrier source-topology
    target-carrier target-distance mapping)
   (q1477053-uniform-closure-law-p
    source-carrier source-topology
    target-carrier target-distance family mapping)))

;; Compactness of the closure in the uniform-convergence topology.

(defun-sk q1477053-function-cover-point-p
    (source-carrier source-topology
     target-carrier target-distance cover mapping)
  (exists (set)
    (and
     (q1477053-valid-function-set-p
      source-carrier source-topology
      target-carrier target-distance set)
     (q1477053-member-p cover set)
     (q1477053-member-p set mapping))))

(defun-sk q1477053-function-cover-closure-p
    (source-carrier source-topology
     target-carrier target-distance family cover)
  (forall (mapping)
    (implies
     (q1477053-in-uniform-closure-p
      source-carrier source-topology
      target-carrier target-distance family mapping)
     (q1477053-function-cover-point-p
      source-carrier source-topology
      target-carrier target-distance cover mapping))))

(defun q1477053-function-finite-subcover-elements-p
    (sets source-carrier source-topology
     target-carrier target-distance cover)
  (if (consp sets)
      (and
       (q1477053-valid-function-set-p
        source-carrier source-topology
        target-carrier target-distance (car sets))
       (q1477053-member-p cover (car sets))
       (q1477053-function-finite-subcover-elements-p
        (cdr sets) source-carrier source-topology
        target-carrier target-distance cover))
    (equal sets nil)))

(defun q1477053-function-finite-subcover-point-p
    (sets mapping)
  (if (consp sets)
      (or
       (q1477053-member-p (car sets) mapping)
       (q1477053-function-finite-subcover-point-p
        (cdr sets) mapping))
    nil))

(defun-sk q1477053-function-finite-subcover-covers-closure-p
    (source-carrier source-topology
     target-carrier target-distance family sets)
  (forall (mapping)
    (implies
     (q1477053-in-uniform-closure-p
      source-carrier source-topology
      target-carrier target-distance family mapping)
     (q1477053-function-finite-subcover-point-p
      sets mapping))))

(defun q1477053-function-finite-subcover-p
    (sets source-carrier source-topology
     target-carrier target-distance family cover)
  (and
   (true-listp sets)
   (q1477053-function-finite-subcover-elements-p
    sets source-carrier source-topology
    target-carrier target-distance cover)
   (q1477053-function-finite-subcover-covers-closure-p
    source-carrier source-topology
    target-carrier target-distance family sets)))

(defun-sk q1477053-function-finite-subcover-exists-p
    (source-carrier source-topology
     target-carrier target-distance family cover)
  (exists (sets)
    (q1477053-function-finite-subcover-p
     sets source-carrier source-topology
     target-carrier target-distance family cover)))

(defun-sk q1477053-uniform-closure-compact-p
    (source-carrier source-topology
     target-carrier target-distance family)
  (forall (cover)
    (implies
     (and
      (q1477053-function-family-of-sets-p
       source-carrier source-topology
       target-carrier target-distance cover)
      (q1477053-function-family-members-uniform-open-p
       source-carrier source-topology
       target-carrier target-distance cover)
      (q1477053-function-cover-closure-p
       source-carrier source-topology
       target-carrier target-distance family cover))
     (q1477053-function-finite-subcover-exists-p
      source-carrier source-topology
      target-carrier target-distance family cover))))

(defun thousand-theorems-q1477053-arzela-ascoli-theorem-statement
    (source-carrier source-topology
     target-carrier target-distance compact-range family)
  (implies
   (and
    (q1477053-topological-space-p
     source-carrier source-topology)
    (q1477053-compact-set-p
     source-carrier source-topology source-carrier)
    (q1477053-metric-space-p
     target-carrier target-distance)
    (q1477053-metric-compact-set-p
     target-carrier target-distance compact-range)
    (q1477053-valid-function-set-p
     source-carrier source-topology
     target-carrier target-distance family)
    (q1477053-family-range-in-set-p
     source-carrier family compact-range)
    (q1477053-equicontinuous-p
     source-carrier source-topology
     target-distance family))
   (q1477053-uniform-closure-compact-p
    source-carrier source-topology
    target-carrier target-distance family)))

(value-triple :itpeval-statement-checked)
:q
