;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__031, "Ramsey's Theorem": every finite coloring of
;; the fixed-cardinality subsets of an arbitrary infinite set has an infinite
;; subset on which the coloring is constant. This file contains no proof.
;; Manual semantic audit (2026-09-06): retained as a historical candidate,
;; but not counted as a faithful standard-ACL2 translation. See
;; corpus-extension/semantic_canonical_resolutions.json for the blocker.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A tame unary function object is a characteristic function for an arbitrary
;; set. A second tame unary function object maps duplicate-free finite lists
;; to colors. Extensionality below makes the latter depend only on the finite
;; set represented by a list, not on the order of its elements.

(defun ht031-member-p (set element)
  (if (apply$ set (list element))
      t
    nil))

(defun ht031-color (coloring finite-subset)
  (apply$ coloring (list finite-subset)))

(defun ht031-elements-in-set-p (set elements)
  (if (consp elements)
      (and
       (ht031-member-p set (car elements))
       (ht031-elements-in-set-p set (cdr elements)))
    (equal elements nil)))

(defun ht031-finite-subset-p (set rank elements)
  (and
   (true-listp elements)
   (no-duplicatesp-equal elements)
   (equal (len elements) rank)
   (ht031-elements-in-set-p set elements)))

(defun ht031-same-finite-set-p (left right)
  (and
   (subsetp-equal left right)
   (subsetp-equal right left)))

(defun-sk ht031-coloring-extensional-p (coloring)
  (forall (left right)
    (implies
     (and
      (true-listp left)
      (true-listp right)
      (no-duplicatesp-equal left)
      (no-duplicatesp-equal right)
      (ht031-same-finite-set-p left right))
     (equal
      (ht031-color coloring left)
      (ht031-color coloring right)))))

(defun-sk ht031-coloring-bounded-p
    (source-set coloring rank color-count)
  (forall (finite-subset)
    (implies
     (ht031-finite-subset-p
      source-set rank finite-subset)
     (and
      (natp (ht031-color coloring finite-subset))
      (< (ht031-color coloring finite-subset)
         color-count)))))

;; An injective sequence N -> S has infinite range contained in S. Conversely,
;; in the classical setting of the source formalizations, every infinite set
;; admits such a sequence. Thus these predicates define infinitude without a
;; finite carrier, a bounded approximation, or an externally supplied witness.

(defun ht031-sequence-value (sequence index)
  (apply$ sequence (list index)))

(defun-sk ht031-sequence-in-set-p (set sequence)
  (forall (index)
    (implies
     (natp index)
     (ht031-member-p
      set
      (ht031-sequence-value sequence index)))))

(defun-sk ht031-sequence-injective-p (sequence)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (equal
       (ht031-sequence-value sequence left-index)
       (ht031-sequence-value sequence right-index)))
     (equal left-index right-index))))

(defun ht031-injective-sequence-in-set-p (set sequence)
  (and
   (tamep-functionp sequence)
   (ht031-sequence-in-set-p set sequence)
   (ht031-sequence-injective-p sequence)))

(defun-sk ht031-infinite-set-p (set)
  (exists (enumeration)
    (ht031-injective-sequence-in-set-p set enumeration)))

(defun ht031-natural-index-list-p (indices)
  (if (consp indices)
      (and
       (natp (car indices))
       (ht031-natural-index-list-p (cdr indices)))
    (equal indices nil)))

(defun ht031-index-subset-p (rank indices)
  (and
   (true-listp indices)
   (no-duplicatesp-equal indices)
   (equal (len indices) rank)
   (ht031-natural-index-list-p indices)))

(defun ht031-sequence-image (sequence indices)
  (if (consp indices)
      (cons
       (ht031-sequence-value sequence (car indices))
       (ht031-sequence-image sequence (cdr indices)))
    nil))

(defun-sk ht031-sequence-homogeneous-p
    (sequence coloring rank homogeneous-color)
  (forall (indices)
    (implies
     (ht031-index-subset-p rank indices)
     (equal
      (ht031-color
       coloring
       (ht031-sequence-image sequence indices))
      homogeneous-color))))

;; The range of HOMOGENEOUS-SEQUENCE is the existential set Y' in the source
;; statements. Injectivity makes that range infinite, and quantification over
;; all finite index sets is equivalent to quantification over all rank-element
;; subsets of the range.

(defun-sk ht031-homogeneous-witness-exists-p
    (source-set coloring rank color-count)
  (exists (homogeneous-sequence homogeneous-color)
    (and
     (natp homogeneous-color)
     (< homogeneous-color color-count)
     (ht031-injective-sequence-in-set-p
      source-set homogeneous-sequence)
     (ht031-sequence-homogeneous-p
      homogeneous-sequence coloring rank homogeneous-color))))

(defun hundred-theorems-031-ramsey-statement
    (rank color-count source-set coloring)
  (implies
   (and
    (natp rank)
    (natp color-count)
    (tamep-functionp source-set)
    (tamep-functionp coloring)
    (ht031-infinite-set-p source-set)
    (ht031-coloring-extensional-p coloring)
    (ht031-coloring-bounded-p
     source-set coloring rank color-count))
   (ht031-homogeneous-witness-exists-p
    source-set coloring rank color-count)))

(value-triple :itpeval-statement-checked)
:q
