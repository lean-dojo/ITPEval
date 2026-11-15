;; Statement-only formalization of thousand-theorems corpus artifact Q468391,
;; "Bolzano–Weierstrass theorem": in a proper pseudometric space, a sequence
;; frequently contained in a bounded set, and in particular a sequence wholly
;; contained in one, has a subsequence converging to its closure. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ functions represent arbitrary carriers, subsets, families, and
;; sequences. Distances are represented exactly by rounded rational upper
;; cuts: DISTANCE-LT-P(d,x,y,q) means d(x,y) < q. Thus the distance may be any
;; finite nonnegative real, not merely a rational. DEFUN-SK keeps all points,
;; sets, covers, indices, limits, and subsequence functions in their source
;; quantifier scopes.

(defun q468391-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q468391-value (function object)
  (apply$ function (list object)))

(defun q468391-distance-lt-p
    (distance left right radius)
  (if (apply$ distance (list left right radius)) t nil))

(defun q468391-positive-rational-p (radius)
  (and
   (rationalp radius)
   (< 0 radius)))

;; Extensional subsets and arbitrary families of subsets.

(defun-sk q468391-set-contained-p (carrier set)
  (forall (x)
    (implies
     (q468391-member-p set x)
     (q468391-member-p carrier x))))

(defun q468391-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q468391-set-contained-p carrier set)))

(defun-sk q468391-set-equiv-p (carrier left right)
  (forall (x)
    (implies
     (q468391-member-p carrier x)
     (iff
      (q468391-member-p left x)
      (q468391-member-p right x)))))

(defun-sk q468391-family-extensional-p (carrier family)
  (forall (left right)
    (implies
     (and
      (q468391-valid-set-p carrier left)
      (q468391-valid-set-p carrier right)
      (q468391-set-equiv-p carrier left right))
     (iff
      (q468391-member-p family left)
      (q468391-member-p family right)))))

(defun-sk q468391-family-members-valid-p (carrier family)
  (forall (set)
    (implies
     (q468391-member-p family set)
     (q468391-valid-set-p carrier set))))

(defun q468391-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q468391-family-extensional-p carrier family)
   (q468391-family-members-valid-p carrier family)))

;; Rounded rational upper cuts for genuine real-valued pseudometrics.

(defun-sk q468391-distance-finite-p
    (distance left right)
  (exists (radius)
    (and
     (q468391-positive-rational-p radius)
     (q468391-distance-lt-p
      distance left right radius))))

(defun-sk q468391-distance-rounded-p
    (distance left right radius)
  (exists (smaller)
    (and
     (q468391-positive-rational-p smaller)
     (rationalp radius)
     (< smaller radius)
     (q468391-distance-lt-p
      distance left right smaller))))

(defun-sk q468391-pseudometric-laws-p
    (carrier distance)
  (forall (x y z q r s)
    (implies
     (and
      (q468391-member-p carrier x)
      (q468391-member-p carrier y)
      (q468391-member-p carrier z))
     (and
      (implies
       (q468391-distance-lt-p distance x y q)
       (q468391-positive-rational-p q))
      (implies
       (and
        (q468391-distance-lt-p distance x y q)
        (rationalp r)
        (< q r))
       (q468391-distance-lt-p distance x y r))
      (implies
       (q468391-distance-lt-p distance x y q)
       (q468391-distance-rounded-p
        distance x y q))
      (q468391-distance-finite-p distance x y)
      (iff
       (q468391-distance-lt-p distance x y q)
       (q468391-distance-lt-p distance y x q))
      (iff
       (q468391-distance-lt-p distance x x q)
       (q468391-positive-rational-p q))
      (implies
       (and
        (q468391-positive-rational-p r)
        (q468391-positive-rational-p s)
        (q468391-distance-lt-p distance x y r)
        (q468391-distance-lt-p distance y z s))
       (q468391-distance-lt-p
        distance x z (+ r s)))))))

(defun q468391-pseudometric-space-p (carrier distance)
  (and
   (tamep-functionp carrier)
   (tamep-functionp distance)
   (q468391-pseudometric-laws-p carrier distance)))

;; The topology induced by the pseudometric.

(defun-sk q468391-metric-ball-subset-p
    (carrier distance center radius set)
  (forall (point)
    (implies
     (and
      (q468391-member-p carrier point)
      (q468391-distance-lt-p
       distance center point radius))
     (q468391-member-p set point))))

(defun-sk q468391-open-radius-exists-p
    (carrier distance set center)
  (exists (radius)
    (and
     (q468391-positive-rational-p radius)
     (q468391-metric-ball-subset-p
      carrier distance center radius set))))

(defun-sk q468391-open-law-p (carrier distance set)
  (forall (center)
    (implies
     (and
      (q468391-member-p carrier center)
      (q468391-member-p set center))
     (q468391-open-radius-exists-p
      carrier distance set center))))

(defun q468391-open-set-p (carrier distance set)
  (and
   (q468391-valid-set-p carrier set)
   (q468391-open-law-p carrier distance set)))

;; Compactness via arbitrary open covers and internal finite subcovers.

(defun-sk q468391-family-members-open-p
    (carrier distance family)
  (forall (set)
    (implies
     (q468391-member-p family set)
     (q468391-open-set-p carrier distance set))))

(defun-sk q468391-cover-point-p (carrier family x)
  (exists (set)
    (and
     (q468391-valid-set-p carrier set)
     (q468391-member-p family set)
     (q468391-member-p set x))))

(defun-sk q468391-cover-p (carrier set family)
  (forall (x)
    (implies
     (and
      (q468391-member-p carrier x)
      (q468391-member-p set x))
     (q468391-cover-point-p carrier family x))))

(defun q468391-finite-subcover-elements-p
    (sets carrier family)
  (if (consp sets)
      (and
       (q468391-valid-set-p carrier (car sets))
       (q468391-member-p family (car sets))
       (q468391-finite-subcover-elements-p
        (cdr sets) carrier family))
    (equal sets nil)))

(defun q468391-finite-subcover-point-p (sets x)
  (if (consp sets)
      (or
       (q468391-member-p (car sets) x)
       (q468391-finite-subcover-point-p (cdr sets) x))
    nil))

(defun-sk q468391-finite-subcover-covers-p
    (carrier set sets)
  (forall (x)
    (implies
     (and
      (q468391-member-p carrier x)
      (q468391-member-p set x))
     (q468391-finite-subcover-point-p sets x))))

(defun q468391-finite-subcover-p
    (sets carrier set family)
  (and
   (true-listp sets)
   (q468391-finite-subcover-elements-p
    sets carrier family)
   (q468391-finite-subcover-covers-p
    carrier set sets)))

(defun-sk q468391-finite-subcover-exists-p
    (carrier set family)
  (exists (sets)
    (q468391-finite-subcover-p
     sets carrier set family)))

(defun-sk q468391-compact-cover-law-p
    (carrier distance set)
  (forall (family)
    (implies
     (and
      (q468391-family-of-sets-p carrier family)
      (q468391-family-members-open-p
       carrier distance family)
      (q468391-cover-p carrier set family))
     (q468391-finite-subcover-exists-p
      carrier set family))))

(defun q468391-compact-set-p (carrier distance set)
  (and
   (q468391-valid-set-p carrier set)
   (q468391-compact-cover-law-p
    carrier distance set)))

;; Metric boundedness.

(defun-sk q468391-bound-p
    (carrier distance set bound)
  (forall (x y)
    (implies
     (and
      (q468391-member-p carrier x)
      (q468391-member-p carrier y)
      (q468391-member-p set x)
      (q468391-member-p set y))
     (q468391-distance-lt-p
      distance x y bound))))

(defun-sk q468391-bounded-witness-exists-p
    (carrier distance set)
  (exists (bound)
    (and
     (q468391-positive-rational-p bound)
     (q468391-bound-p
      carrier distance set bound))))

(defun q468391-bounded-set-p (carrier distance set)
  (and
   (q468391-valid-set-p carrier set)
   (q468391-bounded-witness-exists-p
    carrier distance set)))

;; Properness: every nonnegative rational-radius closed ball is compact.
;; Rational radii are cofinal, so this is equivalent to compactness of all
;; real-radius closed balls.

(defun-sk q468391-distance-le-p
    (distance left right bound)
  (forall (radius)
    (implies
     (and
      (rationalp radius)
      (< bound radius))
     (q468391-distance-lt-p
      distance left right radius))))

(defun-sk q468391-closed-ball-representation-p
    (carrier distance center radius ball)
  (forall (x)
    (implies
     (q468391-member-p carrier x)
     (iff
      (q468391-member-p ball x)
      (q468391-distance-le-p
       distance center x radius)))))

(defun-sk q468391-compact-closed-ball-exists-p
    (carrier distance center radius)
  (exists (ball)
    (and
     (q468391-valid-set-p carrier ball)
     (q468391-closed-ball-representation-p
      carrier distance center radius ball)
     (q468391-compact-set-p
      carrier distance ball))))

(defun-sk q468391-proper-space-p (carrier distance)
  (forall (center radius)
    (implies
     (and
      (q468391-member-p carrier center)
      (rationalp radius)
      (<= 0 radius))
     (q468391-compact-closed-ball-exists-p
      carrier distance center radius))))

;; Closure, natural-number sequences, frequent membership, and convergence.

(defun-sk q468391-closure-witness-exists-p
    (carrier distance set point radius)
  (exists (nearby)
    (and
     (q468391-member-p carrier nearby)
     (q468391-member-p set nearby)
     (q468391-distance-lt-p
      distance point nearby radius))))

(defun-sk q468391-closure-point-p
    (carrier distance set point)
  (forall (radius)
    (implies
     (q468391-positive-rational-p radius)
     (q468391-closure-witness-exists-p
      carrier distance set point radius))))

(defun-sk q468391-sequence-typed-p (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (q468391-member-p
      carrier (q468391-value sequence n)))))

(defun-sk q468391-sequence-in-set-p (set sequence)
  (forall (n)
    (implies
     (natp n)
     (q468391-member-p
      set (q468391-value sequence n)))))

(defun-sk q468391-later-set-index-exists-p
    (set sequence threshold)
  (exists (n)
    (and
     (natp n)
     (<= threshold n)
     (q468391-member-p
      set (q468391-value sequence n)))))

(defun-sk q468391-frequently-in-set-p (set sequence)
  (forall (threshold)
    (implies
     (natp threshold)
     (q468391-later-set-index-exists-p
      set sequence threshold))))

(defun-sk q468391-nat-map-p (map)
  (forall (n)
    (implies
     (natp n)
     (natp (q468391-value map n)))))

(defun-sk q468391-strict-mono-p (map)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (< m n))
     (<
      (q468391-value map m)
      (q468391-value map n)))))

(defun-sk q468391-eventually-close-p
    (distance sequence map point radius threshold)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= threshold n))
     (q468391-distance-lt-p
      distance
      (q468391-value
       sequence (q468391-value map n))
      point
      radius))))

(defun-sk q468391-convergence-threshold-exists-p
    (distance sequence map point radius)
  (exists (threshold)
    (and
     (natp threshold)
     (q468391-eventually-close-p
      distance sequence map point radius threshold))))

(defun-sk q468391-tendsto-subsequence-p
    (distance sequence map point)
  (forall (radius)
    (implies
     (q468391-positive-rational-p radius)
     (q468391-convergence-threshold-exists-p
      distance sequence map point radius))))

(defun-sk q468391-convergent-subsequence-exists-p
    (carrier distance set sequence)
  (exists (point map)
    (and
     (q468391-member-p carrier point)
     (q468391-closure-point-p
      carrier distance set point)
     (tamep-functionp map)
     (q468391-nat-map-p map)
     (q468391-strict-mono-p map)
     (q468391-tendsto-subsequence-p
      distance sequence map point))))

(defun thousand-theorems-q468391-tendsto-subseq-of-frequently-bounded-statement
    (carrier distance set sequence)
  (implies
   (and
    (q468391-pseudometric-space-p carrier distance)
    (q468391-proper-space-p carrier distance)
    (q468391-bounded-set-p carrier distance set)
    (tamep-functionp sequence)
    (q468391-sequence-typed-p carrier sequence)
    (q468391-frequently-in-set-p set sequence))
   (q468391-convergent-subsequence-exists-p
    carrier distance set sequence)))

(defun thousand-theorems-q468391-tendsto-subseq-of-bounded-statement
    (carrier distance set sequence)
  (implies
   (and
    (q468391-pseudometric-space-p carrier distance)
    (q468391-proper-space-p carrier distance)
    (q468391-bounded-set-p carrier distance set)
    (tamep-functionp sequence)
    (q468391-sequence-typed-p carrier sequence)
    (q468391-sequence-in-set-p set sequence))
   (q468391-convergent-subsequence-exists-p
    carrier distance set sequence)))

(value-triple :itpeval-statement-checked)
:q
