;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__082, "Dissection of Cubes (into Cubes)": in every
;; dimension at least three, a nontrivial finite dissection of the unit cube
;; into axis-aligned cubes has two component cubes of equal width. This file
;; contains no proof.

(in-package "ACL2")

;; A cube is represented by (lower-corner width).  The lower corner is an
;; n-list of rational coordinates and the width is a positive rational.
;;
;; This rational representation is bidirectionally equivalent to the finite
;; real-coordinate counterexample statement.  For any real counterexample,
;; the equalities and strict order relations among its finitely many lower and
;; upper faces, together with the fixed faces 0 and 1, form a rational linear
;; system.  A real solution of that system has a rational solution in the same
;; relative open polyhedron, preserving positivity, distinct widths, face
;; incidences, and the tiling.  Conversely, rational coordinates embed in the
;; reals.  Thus quantifying over these rational records does not discard a
;; possible real counterexample.
;;
;; For a finite family of closed cubes contained in the unit cube, pairwise
;; disjoint interiors and total n-volume one are equivalent to covering the
;; unit cube.  This also reconciles the closed-cube and half-open-cube boundary
;; conventions used by the source statements.

(defun ht082-rational-coordinate-list-p (coordinates n)
  (if (zp n)
      (equal coordinates nil)
    (and (consp coordinates)
         (rationalp (car coordinates))
         (ht082-rational-coordinate-list-p
          (cdr coordinates)
          (- n 1)))))

(defun ht082-coordinate-bounds-p (coordinates width)
  (if (consp coordinates)
      (and (<= 0 (car coordinates))
           (<= (+ (car coordinates) width) 1)
           (ht082-coordinate-bounds-p
            (cdr coordinates)
            width))
    (equal coordinates nil)))

(defun ht082-cube-p (cube n)
  (and (true-listp cube)
       (equal (len cube) 2)
       (rationalp (cadr cube))
       (< 0 (cadr cube))
       (ht082-rational-coordinate-list-p (car cube) n)
       (ht082-coordinate-bounds-p (car cube) (cadr cube))))

(defun ht082-cube-list-p (cubes n)
  (if (consp cubes)
      (and (ht082-cube-p (car cubes) n)
           (ht082-cube-list-p (cdr cubes) n))
    (equal cubes nil)))

(defun ht082-cubes-separated-p
    (lower-left width-left lower-right width-right)
  (if (and (consp lower-left)
           (consp lower-right))
      (or (<= (+ (car lower-left) width-left)
              (car lower-right))
          (<= (+ (car lower-right) width-right)
              (car lower-left))
          (ht082-cubes-separated-p
           (cdr lower-left)
           width-left
           (cdr lower-right)
           width-right))
    nil))

(defun ht082-cube-disjoint-from-list-p (cube cubes)
  (if (consp cubes)
      (and (ht082-cubes-separated-p
            (car cube)
            (cadr cube)
            (car (car cubes))
            (cadr (car cubes)))
           (ht082-cube-disjoint-from-list-p cube (cdr cubes)))
    t))

(defun ht082-pairwise-interior-disjoint-p (cubes)
  (if (consp cubes)
      (and (ht082-cube-disjoint-from-list-p
            (car cubes)
            (cdr cubes))
           (ht082-pairwise-interior-disjoint-p (cdr cubes)))
    t))

(defun ht082-total-volume (cubes n)
  (if (consp cubes)
      (+ (expt (cadr (car cubes)) n)
         (ht082-total-volume (cdr cubes) n))
    0))

(defun ht082-width-different-from-list-p (width cubes)
  (if (consp cubes)
      (and (not (equal width (cadr (car cubes))))
           (ht082-width-different-from-list-p width (cdr cubes)))
    t))

(defun ht082-pairwise-distinct-widths-p (cubes)
  (if (consp cubes)
      (and (ht082-width-different-from-list-p
            (cadr (car cubes))
            (cdr cubes))
           (ht082-pairwise-distinct-widths-p (cdr cubes)))
    t))

(defun hundred-theorems-082-dissection-of-cubes-statement (n cubes)
  (implies
   (and (natp n)
        (<= 3 n)
        (true-listp cubes)
        (consp cubes)
        (consp (cdr cubes))
        (ht082-cube-list-p cubes n)
        (ht082-pairwise-interior-disjoint-p cubes)
        (equal (ht082-total-volume cubes n) 1))
   (not (ht082-pairwise-distinct-widths-p cubes))))

(value-triple :itpeval-statement-checked)
:q
