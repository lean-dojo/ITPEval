;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q918099, "Ramsey's theorem": every coloring of
;; the r-element subsets of an infinite subset of the natural numbers by a
;; finite palette has an infinite monochromatic subset. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent arbitrary subsets of the naturals and
;; an arbitrary coloring. Set and coloring tags are observed only through
;; membership and color evaluation, so no finite table replaces either
;; potentially infinite object.

(defstub q918099-set-member-p (set natural) t)
(defstub q918099-color (coloring edge) t)

;; A strictly increasing true list is the unique canonical representation of
;; a finite subset of the naturals. Consequently the arbitrary coloring is
;; applied once per finset, independently of list order.

(defun q918099-strictly-increasing-nat-list-p (values)
  (if (consp values)
      (and
       (natp (car values))
       (if (consp (cdr values))
           (and
            (< (car values) (cadr values))
            (q918099-strictly-increasing-nat-list-p
             (cdr values)))
         (equal (cdr values) nil)))
    (equal values nil)))

(defun q918099-all-members-of-set-p (values set)
  (if (consp values)
      (and
       (q918099-set-member-p set (car values))
       (q918099-all-members-of-set-p (cdr values) set))
    (equal values nil)))

(defun q918099-r-edge-of-set-p (r set edge)
  (and
   (natp r)
   (q918099-strictly-increasing-nat-list-p edge)
   (equal (len edge) r)
   (q918099-all-members-of-set-p edge set)))

;; Duplicate-free true lists represent exactly the source finset K of colors.
;; Colors themselves remain arbitrary ACL2 objects, matching the arbitrary
;; source type alpha on the only part of it used by the statement.

(defun q918099-finite-color-set-p (colors)
  (and
   (true-listp colors)
   (no-duplicatesp-equal colors)))

(defun-sk q918099-coloring-into-p
    (r set colors coloring)
  (forall (edge)
    (implies
     (q918099-r-edge-of-set-p r set edge)
     (member-equal
      (q918099-color coloring edge)
      colors))))

;; For a subset of the naturals, infinitude is equivalent to unboundedness.
;; Both the bound and the larger member remain internal quantifiers.

(defun-sk q918099-member-above-exists-p (set bound)
  (exists (natural)
    (and
     (natp natural)
     (< bound natural)
     (q918099-set-member-p set natural))))

(defun-sk q918099-infinite-nat-set-p (set)
  (forall (bound)
    (implies
     (natp bound)
     (q918099-member-above-exists-p set bound))))

(defun-sk q918099-nat-set-subset-p (subset superset)
  (forall (natural)
    (implies
     (and
      (natp natural)
      (q918099-set-member-p subset natural))
     (q918099-set-member-p superset natural))))

(defun-sk q918099-monochromatic-on-p
    (r set coloring color)
  (forall (edge)
    (implies
     (q918099-r-edge-of-set-p r set edge)
     (equal
      (q918099-color coloring edge)
      color))))

;; The monochromatic subset and common color are existentially quantified
;; inside the conclusion, preserving the source theorem's quantifier scope.

(defun-sk q918099-infinite-monochromatic-subset-exists-p
    (r original-set colors coloring)
  (exists (monochromatic-set color)
    (and
     (q918099-nat-set-subset-p
      monochromatic-set original-set)
     (q918099-infinite-nat-set-p monochromatic-set)
     (member-equal color colors)
     (q918099-monochromatic-on-p
      r monochromatic-set coloring color))))

(defun thousand-theorems-q918099-ramseys-theorem-statement
    (r infinite-set colors coloring)
  (implies
   (and
    (natp r)
    (q918099-finite-color-set-p colors)
    (q918099-infinite-nat-set-p infinite-set)
    (q918099-coloring-into-p
     r infinite-set colors coloring))
   (q918099-infinite-monochromatic-subset-exists-p
    r infinite-set colors coloring)))

(value-triple :itpeval-statement-checked)
:q
