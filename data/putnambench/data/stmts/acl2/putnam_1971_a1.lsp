;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_a1:
;; every set of nine lattice points in three-dimensional Euclidean space has
;; an interior lattice point on a segment joining two distinct set members.
;; This file contains no proof.

(in-package "ACL2")

;; The source set has cardinality nine, so a duplicate-free nine-element list
;; is a bijective representation of it. Each point is an integer coordinate
;; triple. For distinct lattice points P and Q, their open segment contains a
;; lattice point exactly when some integer d >= 2 divides all three coordinate
;; differences: such a d gives P + (Q-P)/d, and conversely the lattice points
;; on the line are spaced by the primitive direction vector. Any such d is at
;; most the largest absolute coordinate difference, so the bounded search is
;; exhaustive. Thus the pair and lattice-point witnesses from the source
;; conclusion remain internal rather than becoming statement parameters.

(defun putnam-1971-a1-integer-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 3)
   (integerp (nth 0 point))
   (integerp (nth 1 point))
   (integerp (nth 2 point))))

(defun putnam-1971-a1-integer-point-list-p (points)
  (if (consp points)
      (and
       (putnam-1971-a1-integer-point-p (car points))
       (putnam-1971-a1-integer-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1971-a1-max2 (left right)
  (if (< left right) right left))

(defun putnam-1971-a1-common-divisor-from-p
    (dx dy dz divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (and (integerp divisor) (< 1 divisor))
      (or
       (and
        (equal (mod dx divisor) 0)
        (equal (mod dy divisor) 0)
        (equal (mod dz divisor) 0))
       (putnam-1971-a1-common-divisor-from-p
        dx dy dz (- divisor 1)))
    nil))

(defun putnam-1971-a1-segment-has-interior-lattice-point-p
    (left right)
  (let* ((dx (abs (- (nth 0 right) (nth 0 left))))
         (dy (abs (- (nth 1 right) (nth 1 left))))
         (dz (abs (- (nth 2 right) (nth 2 left))))
         (bound
          (putnam-1971-a1-max2
           dx (putnam-1971-a1-max2 dy dz))))
    (and
     (not (equal left right))
     (putnam-1971-a1-common-divisor-from-p
      dx dy dz bound))))

(defun putnam-1971-a1-pair-from-point-exists-p
    (left remaining)
  (if (consp remaining)
      (or
       (putnam-1971-a1-segment-has-interior-lattice-point-p
        left (car remaining))
       (putnam-1971-a1-pair-from-point-exists-p
        left (cdr remaining)))
    nil))

(defun putnam-1971-a1-pair-exists-p (points)
  (if (consp points)
      (or
       (putnam-1971-a1-pair-from-point-exists-p
        (car points) (cdr points))
       (putnam-1971-a1-pair-exists-p (cdr points)))
    nil))

(defun putnambench-putnam-1971-a1-statement (points)
  (implies
   (and
    (true-listp points)
    (no-duplicatesp-equal points)
    (equal (len points) 9)
    (putnam-1971-a1-integer-point-list-p points))
   (putnam-1971-a1-pair-exists-p points)))

(value-triple :itpeval-statement-checked)
:q
