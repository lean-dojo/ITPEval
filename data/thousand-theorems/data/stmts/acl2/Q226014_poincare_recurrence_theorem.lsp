;; Statement-only formalization of thousand-theorems corpus artifact Q226014,
;; "Poincaré recurrence theorem": for a conservative nonsingular measurable
;; self-map, almost every point of a null-measurable set returns to that set
;; infinitely often. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; The source proposition uses its measure only through null sets: positivity
;; in conservativity, absolute continuity, null-measurability, and the
;; almost-everywhere conclusion.  Accordingly, MEASURE is presented by its
;; complete sigma-ideal of null sets.  The explicit ideal laws below are
;; bidirectionally equivalent to a measure for this proposition: every measure
;; supplies such an ideal, while any such ideal is realized by the measure
;; taking value zero on ideal members and infinity otherwise.  Thus no real
;; values, arbitrary sets, or functions are replaced by finite data.

(defstub q226014-domain-member-p (domain object) t)
(defstub q226014-set-member-p (set object) t)
(defstub q226014-measurable-set-p (measurable set) t)
(defstub q226014-measure-null-p (measure set) t)
(defstub q226014-function-value (function argument) t)
(defstub q226014-set-sequence-value (sequence index) t)

;; Extensional sets over the arbitrary carrier.

(defun-sk q226014-valid-set-p (domain set)
  (forall (x)
    (implies
     (q226014-set-member-p set x)
     (q226014-domain-member-p domain x))))

(defun-sk q226014-set-equiv-p (domain left right)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (iff
      (q226014-set-member-p left x)
      (q226014-set-member-p right x)))))

(defun-sk q226014-set-subset-p (domain left right)
  (forall (x)
    (implies
     (and
      (q226014-domain-member-p domain x)
      (q226014-set-member-p left x))
     (q226014-set-member-p right x))))

(defun-sk q226014-empty-set-p (domain set)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (not (q226014-set-member-p set x)))))

(defun-sk q226014-complement-set-p (domain set complement)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (iff
      (q226014-set-member-p complement x)
      (not (q226014-set-member-p set x))))))

(defun-sk q226014-symmetric-difference-set-p
    (domain left right difference)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (iff
      (q226014-set-member-p difference x)
      (not
       (iff
        (q226014-set-member-p left x)
        (q226014-set-member-p right x)))))))

(defun-sk q226014-set-sequence-p (domain sequence)
  (forall (n)
    (implies
     (natp n)
     (q226014-valid-set-p
      domain
      (q226014-set-sequence-value sequence n)))))

(defun-sk q226014-sequence-member-exists-p (sequence x)
  (exists (n)
    (and
     (natp n)
     (q226014-set-member-p
      (q226014-set-sequence-value sequence n)
      x))))

(defun-sk q226014-sequence-union-set-p (domain sequence union)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (iff
      (q226014-set-member-p union x)
      (q226014-sequence-member-exists-p sequence x)))))

(defun-sk q226014-preimage-set-p
    (domain function set preimage)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (iff
      (q226014-set-member-p preimage x)
      (q226014-set-member-p
       set
       (q226014-function-value function x))))))

;; Sigma-algebra laws for the source MeasurableSpace.

(defun-sk q226014-measurable-extensional-p (domain measurable)
  (forall (left right)
    (implies
     (and
      (q226014-valid-set-p domain left)
      (q226014-valid-set-p domain right)
      (q226014-set-equiv-p domain left right))
     (iff
      (q226014-measurable-set-p measurable left)
      (q226014-measurable-set-p measurable right)))))

(defun-sk q226014-measurable-valid-p (domain measurable)
  (forall (set)
    (implies
     (q226014-measurable-set-p measurable set)
     (q226014-valid-set-p domain set))))

(defun-sk q226014-measurable-empty-exists-p (domain measurable)
  (exists (empty)
    (and
     (q226014-empty-set-p domain empty)
     (q226014-measurable-set-p measurable empty))))

(defun-sk q226014-measurable-complement-exists-p
    (domain measurable set)
  (exists (complement)
    (and
     (q226014-valid-set-p domain complement)
     (q226014-complement-set-p domain set complement)
     (q226014-measurable-set-p measurable complement))))

(defun-sk q226014-measurable-complements-p (domain measurable)
  (forall (set)
    (implies
     (q226014-measurable-set-p measurable set)
     (q226014-measurable-complement-exists-p
      domain measurable set))))

(defun-sk q226014-sequence-measurable-p (measurable sequence)
  (forall (n)
    (implies
     (natp n)
     (q226014-measurable-set-p
      measurable
      (q226014-set-sequence-value sequence n)))))

(defun-sk q226014-measurable-union-exists-p
    (domain measurable sequence)
  (exists (union)
    (and
     (q226014-valid-set-p domain union)
     (q226014-sequence-union-set-p domain sequence union)
     (q226014-measurable-set-p measurable union))))

(defun-sk q226014-measurable-sequence-unions-p
    (domain measurable)
  (forall (sequence)
    (implies
     (and
      (q226014-set-sequence-p domain sequence)
      (q226014-sequence-measurable-p measurable sequence))
     (q226014-measurable-union-exists-p
      domain measurable sequence))))

(defun q226014-sigma-algebra-p (domain measurable)
  (and
   (q226014-measurable-extensional-p domain measurable)
   (q226014-measurable-valid-p domain measurable)
   (q226014-measurable-empty-exists-p domain measurable)
   (q226014-measurable-complements-p domain measurable)
   (q226014-measurable-sequence-unions-p domain measurable)))

;; The null-set sigma-ideal of the measure.

(defun-sk q226014-null-extensional-p (domain measure)
  (forall (left right)
    (implies
     (and
      (q226014-valid-set-p domain left)
      (q226014-valid-set-p domain right)
      (q226014-set-equiv-p domain left right))
     (iff
      (q226014-measure-null-p measure left)
      (q226014-measure-null-p measure right)))))

(defun-sk q226014-null-valid-p (domain measure)
  (forall (set)
    (implies
     (q226014-measure-null-p measure set)
     (q226014-valid-set-p domain set))))

(defun-sk q226014-empty-null-p (domain measure)
  (forall (empty)
    (implies
     (q226014-empty-set-p domain empty)
     (q226014-measure-null-p measure empty))))

(defun-sk q226014-null-hereditary-p (domain measure)
  (forall (subset set)
    (implies
     (and
      (q226014-valid-set-p domain subset)
      (q226014-measure-null-p measure set)
      (q226014-set-subset-p domain subset set))
     (q226014-measure-null-p measure subset))))

(defun-sk q226014-sequence-null-p (measure sequence)
  (forall (n)
    (implies
     (natp n)
     (q226014-measure-null-p
      measure
      (q226014-set-sequence-value sequence n)))))

(defun-sk q226014-null-countable-unions-p (domain measure)
  (forall (sequence union)
    (implies
     (and
      (q226014-set-sequence-p domain sequence)
      (q226014-sequence-null-p measure sequence)
      (q226014-valid-set-p domain union)
      (q226014-sequence-union-set-p domain sequence union))
     (q226014-measure-null-p measure union))))

(defun q226014-measure-null-ideal-p (domain measure)
  (and
   (q226014-null-extensional-p domain measure)
   (q226014-null-valid-p domain measure)
   (q226014-empty-null-p domain measure)
   (q226014-null-hereditary-p domain measure)
   (q226014-null-countable-unions-p domain measure)))

(defun q226014-measure-space-p (domain measurable measure)
  (and
   (q226014-sigma-algebra-p domain measurable)
   (q226014-measure-null-ideal-p domain measure)))

;; NullMeasurableSet: equality to a measurable set modulo a null symmetric
;; difference.

(defun-sk q226014-null-measurable-witness-exists-p
    (domain measurable measure set)
  (exists (representative difference)
    (and
     (q226014-measurable-set-p measurable representative)
     (q226014-valid-set-p domain difference)
     (q226014-symmetric-difference-set-p
      domain set representative difference)
     (q226014-measure-null-p measure difference))))

(defun q226014-null-measurable-set-p
    (domain measurable measure set)
  (and
   (q226014-valid-set-p domain set)
   (q226014-null-measurable-witness-exists-p
    domain measurable measure set)))

;; Measurable nonsingular self-maps and their iterates.

(defun-sk q226014-self-map-p (domain function)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (q226014-domain-member-p
      domain
      (q226014-function-value function x)))))

(defun-sk q226014-measurable-preimage-exists-p
    (domain measurable function set)
  (exists (preimage)
    (and
     (q226014-valid-set-p domain preimage)
     (q226014-preimage-set-p domain function set preimage)
     (q226014-measurable-set-p measurable preimage))))

(defun-sk q226014-measurable-map-p
    (domain measurable function)
  (forall (set)
    (implies
     (q226014-measurable-set-p measurable set)
     (q226014-measurable-preimage-exists-p
      domain measurable function set))))

(defun-sk q226014-null-preimage-exists-p
    (domain measure function set)
  (exists (preimage)
    (and
     (q226014-valid-set-p domain preimage)
     (q226014-preimage-set-p domain function set preimage)
     (q226014-measure-null-p measure preimage))))

(defun-sk q226014-nonsingular-map-p
    (domain measure function)
  (forall (set)
    (implies
     (q226014-measure-null-p measure set)
     (q226014-null-preimage-exists-p
      domain measure function set))))

(defun q226014-quasi-measure-preserving-p
    (domain measurable measure function)
  (and
   (q226014-self-map-p domain function)
   (q226014-measurable-map-p domain measurable function)
   (q226014-nonsingular-map-p domain measure function)))

(defun q226014-iterate (function n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      x
    (q226014-function-value
     function
     (q226014-iterate function (1- n) x))))

;; Conservativity is the exact source structure field: every measurable
;; non-null set contains a point returning under a nonzero iterate.

(defun-sk q226014-return-witness-exists-p
    (domain function set)
  (exists (x m)
    (and
     (q226014-domain-member-p domain x)
     (q226014-set-member-p set x)
     (natp m)
     (not (equal m 0))
     (q226014-set-member-p
      set
      (q226014-iterate function m x)))))

(defun-sk q226014-conservative-return-law-p
    (domain measurable measure function)
  (forall (set)
    (implies
     (and
      (q226014-measurable-set-p measurable set)
      (not (q226014-measure-null-p measure set)))
     (q226014-return-witness-exists-p
      domain function set))))

(defun q226014-conservative-p
    (domain measurable measure function)
  (and
   (q226014-quasi-measure-preserving-p
    domain measurable measure function)
   (q226014-conservative-return-law-p
    domain measurable measure function)))

;; Frequently atTop on natural iteration indices: beyond every lower bound
;; there is a return time.

(defun-sk q226014-return-after-exists-p
    (function set x lower)
  (exists (n)
    (and
     (natp n)
     (<= lower n)
     (q226014-set-member-p
      set
      (q226014-iterate function n x)))))

(defun-sk q226014-frequently-returns-p
    (function set x)
  (forall (lower)
    (implies
     (natp lower)
     (q226014-return-after-exists-p
      function set x lower))))

;; The complement of the almost-everywhere implication consists precisely of
;; points in S that fail to return frequently.

(defun-sk q226014-recurrence-failure-set-p
    (domain function set failure)
  (forall (x)
    (implies
     (q226014-domain-member-p domain x)
     (iff
      (q226014-set-member-p failure x)
      (and
       (q226014-set-member-p set x)
       (not
        (q226014-frequently-returns-p
         function set x)))))))

(defun-sk q226014-ae-recurrence-p
    (domain measure function set)
  (exists (failure)
    (and
     (q226014-valid-set-p domain failure)
     (q226014-recurrence-failure-set-p
      domain function set failure)
     (q226014-measure-null-p measure failure))))

(defun-sk
    thousand-theorems-q226014-poincare-recurrence-theorem-statement
    ()
  (forall (domain measurable measure function set)
    (implies
     (and
      (q226014-measure-space-p domain measurable measure)
      (q226014-conservative-p
       domain measurable measure function)
      (q226014-null-measurable-set-p
       domain measurable measure set))
     (q226014-ae-recurrence-p
      domain measure function set))))

(value-triple :itpeval-statement-checked)
:q
