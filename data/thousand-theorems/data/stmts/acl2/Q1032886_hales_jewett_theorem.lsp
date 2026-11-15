;; Statement-only formalization of thousand-theorems corpus artifact Q1032886,
;; "Hales–Jewett theorem": for every finite alphabet and finite color type,
;; some finite-dimensional word space has a nondegenerate monochromatic
;; combinatorial line under every coloring. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A finite type is transported to the canonical natural-number carrier of
;; its cardinality. Thus ALPHABET-SIZE, COLOR-COUNT, and DIMENSION represent
;; the source finite types alpha, kappa, and iota up to equivalence.
;;
;; A word in alpha^iota is its base-ALPHABET-SIZE digit list. A coloring is
;; the table of its values on all such words, in base-code order. This is a
;; bijective representation of the complete finite function space, including
;; the empty-type cases.

(defun q1032886-color-list-p (colors color-count)
  (if (consp colors)
      (and
       (natp (car colors))
       (< (car colors) color-count)
       (q1032886-color-list-p
        (cdr colors) color-count))
    (equal colors nil)))

(defun q1032886-coloring-p
    (coloring dimension alphabet-size color-count)
  (and
   (true-listp coloring)
   (equal
    (len coloring)
    (expt alphabet-size dimension))
   (q1032886-color-list-p coloring color-count)))

;; A line pattern has one entry per coordinate. Entries below ALPHABET-SIZE
;; are constants; the entry equal to ALPHABET-SIZE is the variable coordinate
;; marker. Requiring that marker to occur is exactly Line.proper.

(defun q1032886-pattern-entry-list-p
    (pattern alphabet-size)
  (if (consp pattern)
      (and
       (natp (car pattern))
       (<= (car pattern) alphabet-size)
       (q1032886-pattern-entry-list-p
        (cdr pattern) alphabet-size))
    (equal pattern nil)))

(defun q1032886-line-pattern-p
    (pattern dimension alphabet-size)
  (and
   (true-listp pattern)
   (equal (len pattern) dimension)
   (q1032886-pattern-entry-list-p
    pattern alphabet-size)
   (member-equal alphabet-size pattern)))

;; The first pattern entry is the least-significant base digit. Substituting
;; SYMBOL at every variable marker gives the exact word on the line.

(defun q1032886-line-word-index
    (pattern symbol alphabet-size)
  (if (consp pattern)
      (+
       (if (equal (car pattern) alphabet-size)
           symbol
         (car pattern))
       (* alphabet-size
          (q1032886-line-word-index
           (cdr pattern) symbol alphabet-size)))
    0))

(defun q1032886-all-symbols-have-color-p
    (remaining pattern alphabet-size coloring color)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let* ((symbol (- remaining 1))
           (word-index
            (q1032886-line-word-index
             pattern symbol alphabet-size)))
      (and
       (equal (nth word-index coloring) color)
       (q1032886-all-symbols-have-color-p
        (- remaining 1)
        pattern alphabet-size coloring color)))))

(defun q1032886-monochromatic-line-witness-p
    (dimension alphabet-size color-count
               coloring pattern color)
  (and
   (q1032886-line-pattern-p
    pattern dimension alphabet-size)
   (natp color)
   (< color color-count)
   (q1032886-all-symbols-have-color-p
    alphabet-size pattern alphabet-size coloring color)))

;; These three predicates retain the source quantifier order:
;;   exists dimension, forall colorings, exists line, exists color.

(defun-sk q1032886-coloring-has-monochromatic-line-p
    (dimension alphabet-size color-count coloring)
  (exists (pattern color)
    (q1032886-monochromatic-line-witness-p
     dimension alphabet-size color-count
     coloring pattern color)))

(defun-sk q1032886-dimension-works-p
    (dimension alphabet-size color-count)
  (forall (coloring)
    (implies
     (q1032886-coloring-p
      coloring dimension alphabet-size color-count)
     (q1032886-coloring-has-monochromatic-line-p
      dimension alphabet-size color-count coloring))))

(defun-sk q1032886-good-dimension-exists-p
    (alphabet-size color-count)
  (exists (dimension)
    (and
     (natp dimension)
     (q1032886-dimension-works-p
      dimension alphabet-size color-count))))

(defun thousand-theorems-q1032886-hales-jewett-statement
    (alphabet-size color-count)
  (implies
   (and
    (natp alphabet-size)
    (natp color-count))
   (q1032886-good-dimension-exists-p
    alphabet-size color-count)))

(value-triple :itpeval-statement-checked)
:q
