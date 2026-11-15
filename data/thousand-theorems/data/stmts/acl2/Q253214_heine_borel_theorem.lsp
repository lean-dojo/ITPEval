;; Statement-only formalization of thousand-theorems corpus artifact Q253214,
;; "Heine–Borel theorem": in an arbitrary proper metric space, a set is
;; compact if and only if it is closed and bounded. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ functions represent the arbitrary carrier, metric, sets, and
;; open covers. DEFUN-SK supplies all unbounded quantifiers and keeps radius,
;; cover, and finite-subcover witnesses inside their source scopes. Distances
;; are rounded rational upper cuts representing arbitrary finite nonnegative
;; real values rather than a restriction to rational-valued metrics.

(defun q253214-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q253214-distance-lt-p (distance left right radius)
  (if (apply$ distance (list left right radius)) t nil))

(defun q253214-positive-rational-p (radius)
  (and (rationalp radius)
       (< 0 radius)))

;; Extensional subsets and arbitrary families of subsets.

(defun-sk q253214-set-contained-p (carrier set)
  (forall (x)
    (implies
     (q253214-member-p set x)
     (q253214-member-p carrier x))))

(defun q253214-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q253214-set-contained-p carrier set)))

(defun-sk q253214-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q253214-member-p carrier x)
     (iff
      (q253214-member-p left x)
      (q253214-member-p right x)))))

(defun-sk q253214-family-extensional-p (carrier family)
  (forall (left right)
    (implies
     (and
      (q253214-valid-set-p carrier left)
      (q253214-valid-set-p carrier right)
      (q253214-set-equiv-p carrier left right))
     (iff
      (q253214-member-p family left)
      (q253214-member-p family right)))))

(defun-sk q253214-family-members-valid-p (carrier family)
  (forall (set)
    (implies
     (q253214-member-p family set)
     (q253214-valid-set-p carrier set))))

(defun q253214-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q253214-family-extensional-p carrier family)
   (q253214-family-members-valid-p carrier family)))

;; Rounded rational upper cuts for genuine real-valued metrics.

(defun-sk q253214-distance-finite-p (distance left right)
  (exists (radius)
    (and
     (q253214-positive-rational-p radius)
     (q253214-distance-lt-p
      distance left right radius))))

(defun-sk q253214-distance-rounded-p
    (distance left right radius)
  (exists (smaller)
    (and
     (q253214-positive-rational-p smaller)
     (rationalp radius)
     (< smaller radius)
     (q253214-distance-lt-p
      distance left right smaller))))

(defun-sk q253214-positive-distance-p (distance left right)
  (exists (radius)
    (and
     (q253214-positive-rational-p radius)
     (not
      (q253214-distance-lt-p
       distance left right radius)))))

(defun-sk q253214-metric-laws-p (carrier distance)
  (forall (x y z q r s)
    (implies
     (and
      (q253214-member-p carrier x)
      (q253214-member-p carrier y)
      (q253214-member-p carrier z))
     (and
      (implies
       (q253214-distance-lt-p distance x y q)
       (q253214-positive-rational-p q))
      (implies
       (and
        (q253214-distance-lt-p distance x y q)
        (rationalp r)
        (< q r))
       (q253214-distance-lt-p distance x y r))
      (implies
       (q253214-distance-lt-p distance x y q)
       (q253214-distance-rounded-p
        distance x y q))
      (q253214-distance-finite-p distance x y)
      (iff
       (q253214-distance-lt-p distance x y q)
       (q253214-distance-lt-p distance y x q))
      (iff
       (q253214-distance-lt-p distance x x q)
       (q253214-positive-rational-p q))
      (implies
       (not (equal x y))
       (q253214-positive-distance-p distance x y))
      (implies
       (and
        (q253214-positive-rational-p r)
        (q253214-positive-rational-p s)
        (q253214-distance-lt-p distance x y r)
        (q253214-distance-lt-p distance y z s))
       (q253214-distance-lt-p
        distance x z (+ r s)))))))

(defun q253214-metric-space-p (carrier distance)
  (and
   (tamep-functionp carrier)
   (tamep-functionp distance)
   (q253214-metric-laws-p carrier distance)))

;; The topology induced by the metric.

(defun-sk q253214-metric-ball-subset-p
    (carrier distance center radius set)
  (forall (point)
    (implies
     (and
      (q253214-member-p carrier point)
      (q253214-distance-lt-p
       distance center point radius))
     (q253214-member-p set point))))

(defun-sk q253214-open-radius-exists-p
    (carrier distance set center)
  (exists (radius)
    (and
     (q253214-positive-rational-p radius)
     (q253214-metric-ball-subset-p
      carrier distance center radius set))))

(defun-sk q253214-open-law-p (carrier distance set)
  (forall (center)
    (implies
     (and
      (q253214-member-p carrier center)
      (q253214-member-p set center))
     (q253214-open-radius-exists-p
      carrier distance set center))))

(defun q253214-open-set-p (carrier distance set)
  (and
   (q253214-valid-set-p carrier set)
   (q253214-open-law-p carrier distance set)))

(defun-sk q253214-complement-representation-p
    (carrier set complement)
  (forall (x)
    (implies
     (q253214-member-p carrier x)
     (iff
      (q253214-member-p complement x)
      (not (q253214-member-p set x))))))

(defun-sk q253214-open-complement-exists-p
    (carrier distance set)
  (exists (complement)
    (and
     (q253214-valid-set-p carrier complement)
     (q253214-complement-representation-p
      carrier set complement)
     (q253214-open-set-p
      carrier distance complement))))

(defun q253214-closed-set-p (carrier distance set)
  (and
   (q253214-valid-set-p carrier set)
   (q253214-open-complement-exists-p
    carrier distance set)))

;; Compactness via unrestricted open covers and internal finite subcovers.

(defun-sk q253214-family-members-open-p
    (carrier distance family)
  (forall (set)
    (implies
     (q253214-member-p family set)
     (q253214-open-set-p carrier distance set))))

(defun-sk q253214-cover-point-p (carrier family x)
  (exists (set)
    (and
     (q253214-valid-set-p carrier set)
     (q253214-member-p family set)
     (q253214-member-p set x))))

(defun-sk q253214-cover-p (carrier set family)
  (forall (x)
    (implies
     (and
      (q253214-member-p carrier x)
      (q253214-member-p set x))
     (q253214-cover-point-p carrier family x))))

(defun q253214-finite-subcover-elements-p
    (sets carrier family)
  (if (consp sets)
      (and
       (q253214-valid-set-p carrier (car sets))
       (q253214-member-p family (car sets))
       (q253214-finite-subcover-elements-p
        (cdr sets) carrier family))
    (equal sets nil)))

(defun q253214-finite-subcover-point-p (sets x)
  (if (consp sets)
      (or
       (q253214-member-p (car sets) x)
       (q253214-finite-subcover-point-p (cdr sets) x))
    nil))

(defun-sk q253214-finite-subcover-covers-p
    (carrier set sets)
  (forall (x)
    (implies
     (and
      (q253214-member-p carrier x)
      (q253214-member-p set x))
     (q253214-finite-subcover-point-p sets x))))

(defun q253214-finite-subcover-p
    (sets carrier set family)
  (and
   (true-listp sets)
   (q253214-finite-subcover-elements-p
    sets carrier family)
   (q253214-finite-subcover-covers-p
    carrier set sets)))

(defun-sk q253214-finite-subcover-exists-p
    (carrier set family)
  (exists (sets)
    (q253214-finite-subcover-p
     sets carrier set family)))

(defun-sk q253214-compact-cover-law-p
    (carrier distance set)
  (forall (family)
    (implies
     (and
      (q253214-family-of-sets-p carrier family)
      (q253214-family-members-open-p
       carrier distance family)
      (q253214-cover-p carrier set family))
     (q253214-finite-subcover-exists-p
      carrier set family))))

(defun q253214-compact-set-p (carrier distance set)
  (and
   (q253214-valid-set-p carrier set)
   (q253214-compact-cover-law-p
    carrier distance set)))

;; Metric boundedness.

(defun-sk q253214-bound-p
    (carrier distance set bound)
  (forall (x y)
    (implies
     (and
      (q253214-member-p carrier x)
      (q253214-member-p carrier y)
      (q253214-member-p set x)
      (q253214-member-p set y))
     (q253214-distance-lt-p
      distance x y bound))))

(defun-sk q253214-bounded-witness-exists-p
    (carrier distance set)
  (exists (bound)
    (and
     (q253214-positive-rational-p bound)
     (q253214-bound-p
      carrier distance set bound))))

(defun q253214-bounded-set-p (carrier distance set)
  (and
   (q253214-valid-set-p carrier set)
   (q253214-bounded-witness-exists-p
    carrier distance set)))

;; Properness: every nonnegative rational-radius closed ball is compact.
;; This is equivalent to compactness of every real-radius closed ball because
;; rational radii are cofinal and smaller closed balls are closed subsets.

(defun-sk q253214-distance-le-p
    (distance left right bound)
  (forall (radius)
    (implies
     (and
      (rationalp radius)
      (< bound radius))
     (q253214-distance-lt-p
      distance left right radius))))

(defun-sk q253214-closed-ball-representation-p
    (carrier distance center radius ball)
  (forall (x)
    (implies
     (q253214-member-p carrier x)
     (iff
      (q253214-member-p ball x)
      (q253214-distance-le-p
       distance center x radius)))))

(defun-sk q253214-compact-closed-ball-exists-p
    (carrier distance center radius)
  (exists (ball)
    (and
     (q253214-valid-set-p carrier ball)
     (q253214-closed-ball-representation-p
      carrier distance center radius ball)
     (q253214-compact-set-p
      carrier distance ball))))

(defun-sk q253214-proper-space-p (carrier distance)
  (forall (center radius)
    (implies
     (and
      (q253214-member-p carrier center)
      (rationalp radius)
      (<= 0 radius))
     (q253214-compact-closed-ball-exists-p
      carrier distance center radius))))

(defun thousand-theorems-q253214-heine-borel-theorem-statement
    (carrier distance set)
  (implies
   (and
    (q253214-metric-space-p carrier distance)
    (q253214-proper-space-p carrier distance)
    (q253214-valid-set-p carrier set))
   (iff
    (q253214-compact-set-p carrier distance set)
    (and
     (q253214-closed-set-p carrier distance set)
     (q253214-bounded-set-p carrier distance set)))))

(value-triple :itpeval-statement-checked)
:q
