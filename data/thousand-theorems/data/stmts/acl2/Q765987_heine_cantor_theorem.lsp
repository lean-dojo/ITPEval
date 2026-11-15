;; Statement-only formalization of thousand-theorems corpus artifact Q765987,
;; "Heine–Cantor theorem": every continuous map from a compact uniform space
;; to an arbitrary uniform space is uniformly continuous. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, entourage bases, subsets, open covers, and functions
;; are represented by conservative fixed-arity interfaces.  The uniform-space
;; axioms below are the standard entourage-basis axioms.  The induced topology
;; is defined by entourage neighborhoods, and compactness uses unrestricted
;; open covers with internally quantified finite subcovers.

(defstub q765987-carrier-p (space value) t)
(defstub q765987-entourage-p (space entourage) t)
(defstub q765987-entourage-member-p
    (space entourage left right) t)
(defstub q765987-set-member-p (space set value) t)
(defstub q765987-family-member-p (space family set) t)
(defstub q765987-function-value (function argument) t)

;; Entourage bases for arbitrary uniform spaces.

(defun-sk q765987-entourage-subset-p
    (space left right)
  (forall (x y)
    (implies
     (and
      (q765987-carrier-p space x)
      (q765987-carrier-p space y)
      (q765987-entourage-member-p space left x y))
     (q765987-entourage-member-p space right x y))))

(defun-sk q765987-entourage-exists-p (space)
  (exists (entourage)
    (q765987-entourage-p space entourage)))

(defun-sk q765987-diagonal-law-p (space)
  (forall (entourage x)
    (implies
     (and
      (q765987-entourage-p space entourage)
      (q765987-carrier-p space x))
     (q765987-entourage-member-p
      space entourage x x))))

(defun-sk q765987-common-refinement-exists-p
    (space left right)
  (exists (refinement)
    (and
     (q765987-entourage-p space refinement)
     (q765987-entourage-subset-p
      space refinement left)
     (q765987-entourage-subset-p
      space refinement right))))

(defun-sk q765987-directed-law-p (space)
  (forall (left right)
    (implies
     (and
      (q765987-entourage-p space left)
      (q765987-entourage-p space right))
     (q765987-common-refinement-exists-p
      space left right))))

(defun-sk q765987-symmetric-refinement-p
    (space entourage refinement)
  (forall (x y)
    (implies
     (and
      (q765987-carrier-p space x)
      (q765987-carrier-p space y)
      (q765987-entourage-member-p
       space refinement x y))
     (q765987-entourage-member-p
      space entourage y x))))

(defun-sk q765987-symmetric-refinement-exists-p
    (space entourage)
  (exists (refinement)
    (and
     (q765987-entourage-p space refinement)
     (q765987-symmetric-refinement-p
      space entourage refinement))))

(defun-sk q765987-symmetry-law-p (space)
  (forall (entourage)
    (implies
     (q765987-entourage-p space entourage)
     (q765987-symmetric-refinement-exists-p
      space entourage))))

(defun-sk q765987-square-refinement-p
    (space entourage refinement)
  (forall (x y z)
    (implies
     (and
      (q765987-carrier-p space x)
      (q765987-carrier-p space y)
      (q765987-carrier-p space z)
      (q765987-entourage-member-p
       space refinement x y)
      (q765987-entourage-member-p
       space refinement y z))
     (q765987-entourage-member-p
      space entourage x z))))

(defun-sk q765987-square-refinement-exists-p
    (space entourage)
  (exists (refinement)
    (and
     (q765987-entourage-p space refinement)
     (q765987-square-refinement-p
      space entourage refinement))))

(defun-sk q765987-square-law-p (space)
  (forall (entourage)
    (implies
     (q765987-entourage-p space entourage)
     (q765987-square-refinement-exists-p
      space entourage))))

(defun q765987-uniform-space-p (space)
  (and
   (q765987-entourage-exists-p space)
   (q765987-diagonal-law-p space)
   (q765987-directed-law-p space)
   (q765987-symmetry-law-p space)
   (q765987-square-law-p space)))

;; The topology induced by an entourage basis.

(defun-sk q765987-valid-set-p (space set)
  (forall (x)
    (implies
     (q765987-set-member-p space set x)
     (q765987-carrier-p space x))))

(defun-sk q765987-entourage-ball-subset-p
    (space entourage center set)
  (forall (point)
    (implies
     (and
      (q765987-carrier-p space point)
      (q765987-entourage-member-p
       space entourage center point))
     (q765987-set-member-p space set point))))

(defun-sk q765987-open-neighborhood-exists-p
    (space set center)
  (exists (entourage)
    (and
     (q765987-entourage-p space entourage)
     (q765987-entourage-ball-subset-p
      space entourage center set))))

(defun-sk q765987-open-law-p (space set)
  (forall (center)
    (implies
     (and
      (q765987-carrier-p space center)
      (q765987-set-member-p space set center))
     (q765987-open-neighborhood-exists-p
      space set center))))

(defun q765987-open-set-p (space set)
  (and
   (q765987-valid-set-p space set)
   (q765987-open-law-p space set)))

;; Extensional open covers and finite subcovers.

(defun-sk q765987-set-equiv-p
    (space left right)
  (forall (x)
    (implies
     (q765987-carrier-p space x)
     (iff
      (q765987-set-member-p space left x)
      (q765987-set-member-p space right x)))))

(defun-sk q765987-family-extensional-p
    (space family)
  (forall (left right)
    (implies
     (and
      (q765987-valid-set-p space left)
      (q765987-valid-set-p space right)
      (q765987-set-equiv-p space left right))
     (iff
      (q765987-family-member-p
       space family left)
      (q765987-family-member-p
       space family right)))))

(defun-sk q765987-family-members-valid-p
    (space family)
  (forall (set)
    (implies
     (q765987-family-member-p space family set)
     (q765987-valid-set-p space set))))

(defun q765987-family-of-sets-p
    (space family)
  (and
   (q765987-family-extensional-p space family)
   (q765987-family-members-valid-p space family)))

(defun-sk q765987-family-members-open-p
    (space family)
  (forall (set)
    (implies
     (q765987-family-member-p space family set)
     (q765987-open-set-p space set))))

(defun-sk q765987-cover-point-p
    (space family point)
  (exists (set)
    (and
     (q765987-family-member-p space family set)
     (q765987-set-member-p space set point))))

(defun-sk q765987-cover-p (space family)
  (forall (point)
    (implies
     (q765987-carrier-p space point)
     (q765987-cover-point-p
      space family point))))

(defun q765987-finite-subcover-elements-p
    (sets space family)
  (if (consp sets)
      (and
       (q765987-valid-set-p space (car sets))
       (q765987-family-member-p
        space family (car sets))
       (q765987-finite-subcover-elements-p
        (cdr sets) space family))
    (equal sets nil)))

(defun q765987-finite-subcover-point-p
    (sets space point)
  (if (consp sets)
      (or
       (q765987-set-member-p
        space (car sets) point)
       (q765987-finite-subcover-point-p
        (cdr sets) space point))
    nil))

(defun-sk q765987-finite-subcover-covers-p
    (sets space)
  (forall (point)
    (implies
     (q765987-carrier-p space point)
     (q765987-finite-subcover-point-p
      sets space point))))

(defun q765987-finite-subcover-p
    (sets space family)
  (and
   (true-listp sets)
   (q765987-finite-subcover-elements-p
    sets space family)
   (q765987-finite-subcover-covers-p
    sets space)))

(defun-sk q765987-finite-subcover-exists-p
    (space family)
  (exists (sets)
    (q765987-finite-subcover-p
     sets space family)))

(defun-sk q765987-compact-cover-law-p (space)
  (forall (family)
    (implies
     (and
      (q765987-family-of-sets-p space family)
      (q765987-family-members-open-p space family)
      (q765987-cover-p space family))
     (q765987-finite-subcover-exists-p
      space family))))

(defun q765987-compact-space-p (space)
  (q765987-compact-cover-law-p space))

;; Maps, continuity, and uniform continuity in entourage-basis form.

(defun-sk q765987-map-into-p
    (source target function)
  (forall (x)
    (implies
     (q765987-carrier-p source x)
     (q765987-carrier-p
      target
      (q765987-function-value function x)))))

(defun-sk q765987-continuity-bound-p
    (source target function center
     target-entourage source-entourage)
  (forall (point)
    (implies
     (and
      (q765987-carrier-p source point)
      (q765987-entourage-member-p
       source source-entourage center point))
     (q765987-entourage-member-p
      target
      target-entourage
      (q765987-function-value function center)
      (q765987-function-value function point)))))

(defun-sk q765987-continuity-bound-exists-p
    (source target function center target-entourage)
  (exists (source-entourage)
    (and
     (q765987-entourage-p
      source source-entourage)
     (q765987-continuity-bound-p
      source target function center
      target-entourage source-entourage))))

(defun-sk q765987-continuity-law-p
    (source target function)
  (forall (center target-entourage)
    (implies
     (and
      (q765987-carrier-p source center)
      (q765987-entourage-p
       target target-entourage))
     (q765987-continuity-bound-exists-p
      source target function center
      target-entourage))))

(defun q765987-continuous-map-p
    (source target function)
  (and
   (q765987-map-into-p source target function)
   (q765987-continuity-law-p
    source target function)))

(defun-sk q765987-uniform-bound-p
    (source target function
     target-entourage source-entourage)
  (forall (left right)
    (implies
     (and
      (q765987-carrier-p source left)
      (q765987-carrier-p source right)
      (q765987-entourage-member-p
       source source-entourage left right))
     (q765987-entourage-member-p
      target
      target-entourage
      (q765987-function-value function left)
      (q765987-function-value function right)))))

(defun-sk q765987-uniform-bound-exists-p
    (source target function target-entourage)
  (exists (source-entourage)
    (and
     (q765987-entourage-p
      source source-entourage)
     (q765987-uniform-bound-p
      source target function
      target-entourage source-entourage))))

(defun-sk q765987-uniform-continuous-p
    (source target function)
  (forall (target-entourage)
    (implies
     (q765987-entourage-p
      target target-entourage)
     (q765987-uniform-bound-exists-p
      source target function target-entourage))))

(defun-sk
    thousand-theorems-q765987-heine-cantor-theorem-statement
    ()
  (forall (source target function)
    (implies
     (and
      (q765987-uniform-space-p source)
      (q765987-uniform-space-p target)
      (q765987-compact-space-p source)
      (q765987-continuous-map-p
       source target function))
     (q765987-uniform-continuous-p
      source target function))))

(value-triple :itpeval-statement-checked)
:q
