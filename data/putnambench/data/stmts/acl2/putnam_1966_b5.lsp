;; Statement-only formalization of PutnamBench artifact putnam_1966_b5:
;; every finite set of at least three real planar points in general position
;; is the vertex set of a simple closed polygon. This file contains no proof.

(in-package "ACL2")

;; A duplicate-free finite list is an enumeration of the source finite set.
;; Enumerating every permutation below keeps the existential cyclic ordering
;; internal; a length-n list is exactly a function on ZMod n.
;;
;; ACL2's exact ordered arithmetic is rational. This universal rational
;; encoding is bidirectionally equivalent to the source theorem over real
;; coordinates. For any finite real configuration in general position, all
;; triple-orientation determinants are nonzero, so a sufficiently small
;; coordinate-wise rational perturbation preserves all their signs. In
;; general position, two nonadjacent closed segments intersect exactly when
;; their endpoint orientations have opposite signs on both supporting lines.
;; Hence polygon simplicity depends only on the preserved orientation signs.
;; A simple ordering of the rational perturbation gives the same simple
;; ordering of the original real points. Conversely, rational configurations
;; are real configurations.

(defun putnam-1966-b5-point-p (point)
  (and (true-listp point)
       (equal (len point) 2)
       (rationalp (nth 0 point))
       (rationalp (nth 1 point))))

(defun putnam-1966-b5-point-list-p (points)
  (if (consp points)
      (and (putnam-1966-b5-point-p (car points))
           (putnam-1966-b5-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1966-b5-orientation (a b c)
  (- (* (- (nth 0 b) (nth 0 a))
        (- (nth 1 c) (nth 1 a)))
     (* (- (nth 1 b) (nth 1 a))
        (- (nth 0 c) (nth 0 a)))))

(defun putnam-1966-b5-noncollinear-with-pair-p
    (a b remaining)
  (if (consp remaining)
      (and
       (not (equal
             (putnam-1966-b5-orientation a b (car remaining))
             0))
       (putnam-1966-b5-noncollinear-with-pair-p
        a b (cdr remaining)))
    t))

(defun putnam-1966-b5-noncollinear-with-first-p
    (a remaining)
  (if (consp remaining)
      (and
       (putnam-1966-b5-noncollinear-with-pair-p
        a (car remaining) (cdr remaining))
       (putnam-1966-b5-noncollinear-with-first-p
        a (cdr remaining)))
    t))

(defun putnam-1966-b5-general-position-p (points)
  (if (consp points)
      (and
       (putnam-1966-b5-noncollinear-with-first-p
        (car points) (cdr points))
       (putnam-1966-b5-general-position-p (cdr points)))
    t))

(defun putnam-1966-b5-prepend-to-each (value lists)
  (if (consp lists)
      (cons (cons value (car lists))
            (putnam-1966-b5-prepend-to-each
             value (cdr lists)))
    nil))

(defun putnam-1966-b5-insert-everywhere (value values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (cons
       (cons value values)
       (putnam-1966-b5-prepend-to-each
        (car values)
        (putnam-1966-b5-insert-everywhere
         value (cdr values))))
    (list (list value))))

(defun putnam-1966-b5-insert-into-permutations
    (value permutations)
  (if (consp permutations)
      (append
       (putnam-1966-b5-insert-everywhere
        value (car permutations))
       (putnam-1966-b5-insert-into-permutations
        value (cdr permutations)))
    nil))

(defun putnam-1966-b5-permutations (values)
  (if (consp values)
      (putnam-1966-b5-insert-into-permutations
       (car values)
       (putnam-1966-b5-permutations (cdr values)))
    (list nil)))

(defun putnam-1966-b5-cyclic-edges-aux
    (remaining first)
  (if (consp remaining)
      (if (consp (cdr remaining))
          (cons
           (list (car remaining) (cadr remaining))
           (putnam-1966-b5-cyclic-edges-aux
            (cdr remaining) first))
        (list (list (car remaining) first)))
    nil))

(defun putnam-1966-b5-cyclic-edges (ordering)
  (if (consp ordering)
      (putnam-1966-b5-cyclic-edges-aux
       ordering (car ordering))
    nil))

(defun putnam-1966-b5-edges-share-endpoint-p
    (first-edge second-edge)
  (let ((a (nth 0 first-edge))
        (b (nth 1 first-edge))
        (c (nth 0 second-edge))
        (d (nth 1 second-edge)))
    (or (equal a c)
        (equal a d)
        (equal b c)
        (equal b d))))

(defun putnam-1966-b5-proper-crossing-p
    (first-edge second-edge)
  (let ((a (nth 0 first-edge))
        (b (nth 1 first-edge))
        (c (nth 0 second-edge))
        (d (nth 1 second-edge)))
    (and
     (< (* (putnam-1966-b5-orientation a b c)
           (putnam-1966-b5-orientation a b d))
        0)
     (< (* (putnam-1966-b5-orientation c d a)
           (putnam-1966-b5-orientation c d b))
        0))))

(defun putnam-1966-b5-compatible-edge-p
    (first-edge second-edge)
  (or
   (putnam-1966-b5-edges-share-endpoint-p
    first-edge second-edge)
   (not
    (putnam-1966-b5-proper-crossing-p
     first-edge second-edge))))

(defun putnam-1966-b5-compatible-with-edge-p
    (edge remaining-edges)
  (if (consp remaining-edges)
      (and
       (putnam-1966-b5-compatible-edge-p
        edge (car remaining-edges))
       (putnam-1966-b5-compatible-with-edge-p
        edge (cdr remaining-edges)))
    t))

(defun putnam-1966-b5-all-edges-compatible-p (edges)
  (if (consp edges)
      (and
       (putnam-1966-b5-compatible-with-edge-p
        (car edges) (cdr edges))
       (putnam-1966-b5-all-edges-compatible-p
        (cdr edges)))
    t))

(defun putnam-1966-b5-simple-ordering-p (ordering)
  (putnam-1966-b5-all-edges-compatible-p
   (putnam-1966-b5-cyclic-edges ordering)))

(defun putnam-1966-b5-some-simple-ordering-p (orderings)
  (if (consp orderings)
      (or
       (putnam-1966-b5-simple-ordering-p (car orderings))
       (putnam-1966-b5-some-simple-ordering-p
        (cdr orderings)))
    nil))

(defun putnambench-putnam-1966-b5-statement (points)
  (implies
   (and
    (true-listp points)
    (<= 3 (len points))
    (putnam-1966-b5-point-list-p points)
    (no-duplicatesp-equal points)
    (putnam-1966-b5-general-position-p points))
   (putnam-1966-b5-some-simple-ordering-p
    (putnam-1966-b5-permutations points))))

(value-triple :itpeval-statement-checked)
:q
