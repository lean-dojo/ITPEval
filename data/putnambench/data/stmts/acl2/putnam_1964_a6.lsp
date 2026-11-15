;; Statement-only formalization of PutnamBench artifact putnam_1964_a6:
;; repeated nonmaximal distances in a finite set of real collinear points
;; force every ratio of two pair distances to be rational. This file contains
;; no proof.

(in-package "ACL2")

;; A finite set of reals is represented exactly by rational coordinate
;; vectors in a basis of its finite-dimensional Q-span.  PROBE is a rational
;; linear functional that preserves the order of the represented points and
;; separates distinct pair-distance vectors.  Such a probe exists because
;; only finitely many strict comparisons and hyperplanes must be avoided.
;;
;; Conversely, for any valid finite vector representation, the rational probe
;; can be perturbed arbitrarily slightly to a Q-linearly independent real
;; tuple without changing those finitely many comparisons.  Dot product with
;; that tuple embeds the vectors into the reals.  It preserves point order,
;; distance equality and distance order, while two positive distances have a
;; rational ratio exactly when their rational coordinate vectors are
;; proportional.  Thus the representation is bidirectionally equivalent to
;; the finite-real-set statement, rather than a restriction to rational
;; points.

(defun putnam-1964-a6-rational-vector-p (vector width)
  (if (consp vector)
      (and (rationalp (car vector))
           (putnam-1964-a6-rational-vector-p
            (cdr vector) (- width 1)))
    (and (equal vector nil)
         (equal width 0))))

(defun putnam-1964-a6-point-list-p (points width)
  (if (consp points)
      (and (putnam-1964-a6-rational-vector-p
            (car points) width)
           (putnam-1964-a6-point-list-p
            (cdr points) width))
    (equal points nil)))

(defun putnam-1964-a6-dot-product (left right)
  (if (and (consp left) (consp right))
      (+ (* (car left) (car right))
         (putnam-1964-a6-dot-product
          (cdr left) (cdr right)))
    0))

(defun putnam-1964-a6-vector-subtract (left right)
  (if (and (consp left) (consp right))
      (cons (- (car left) (car right))
            (putnam-1964-a6-vector-subtract
             (cdr left) (cdr right)))
    nil))

(defun putnam-1964-a6-projections-differ-from-p
    (point remaining probe)
  (if (consp remaining)
      (and
       (not
        (equal
         (putnam-1964-a6-dot-product point probe)
         (putnam-1964-a6-dot-product
          (car remaining) probe)))
       (putnam-1964-a6-projections-differ-from-p
        point (cdr remaining) probe))
    t))

(defun putnam-1964-a6-point-projections-distinct-p
    (points probe)
  (if (consp points)
      (and
       (putnam-1964-a6-projections-differ-from-p
        (car points) (cdr points) probe)
       (putnam-1964-a6-point-projections-distinct-p
        (cdr points) probe))
    t))

(defun putnam-1964-a6-pairs-with-first
    (point remaining probe)
  (if (consp remaining)
      (let ((other (car remaining)))
        (cons
         (if (< (putnam-1964-a6-dot-product point probe)
                (putnam-1964-a6-dot-product other probe))
             (list point other)
           (list other point))
         (putnam-1964-a6-pairs-with-first
          point (cdr remaining) probe)))
    nil))

(defun putnam-1964-a6-pairs (points probe)
  (if (consp points)
      (append
       (putnam-1964-a6-pairs-with-first
        (car points) (cdr points) probe)
       (putnam-1964-a6-pairs (cdr points) probe))
    nil))

(defun putnam-1964-a6-pair-distance (pair)
  (putnam-1964-a6-vector-subtract
   (cadr pair) (car pair)))

(defun putnam-1964-a6-distance-value (pair probe)
  (putnam-1964-a6-dot-product
   (putnam-1964-a6-pair-distance pair)
   probe))

(defun putnam-1964-a6-distance-separated-from-p
    (pair remaining probe)
  (if (consp remaining)
      (let ((left-distance
             (putnam-1964-a6-pair-distance pair))
            (right-distance
             (putnam-1964-a6-pair-distance
              (car remaining))))
        (and
         (implies
          (not (equal left-distance right-distance))
          (not
           (equal
            (putnam-1964-a6-dot-product
             left-distance probe)
            (putnam-1964-a6-dot-product
             right-distance probe))))
         (putnam-1964-a6-distance-separated-from-p
          pair (cdr remaining) probe)))
    t))

(defun putnam-1964-a6-distance-projections-separated-p
    (pairs probe)
  (if (consp pairs)
      (and
       (putnam-1964-a6-distance-separated-from-p
        (car pairs) (cdr pairs) probe)
       (putnam-1964-a6-distance-projections-separated-p
        (cdr pairs) probe))
    t))

(defun putnam-1964-a6-has-longer-distance-p
    (pair pairs probe)
  (if (consp pairs)
      (or
       (< (putnam-1964-a6-distance-value pair probe)
          (putnam-1964-a6-distance-value
           (car pairs) probe))
       (putnam-1964-a6-has-longer-distance-p
        pair (cdr pairs) probe))
    nil))

(defun putnam-1964-a6-has-other-equal-distance-p
    (pair pairs)
  (if (consp pairs)
      (or
       (and
        (not (equal pair (car pairs)))
        (equal
         (putnam-1964-a6-pair-distance pair)
         (putnam-1964-a6-pair-distance
          (car pairs))))
       (putnam-1964-a6-has-other-equal-distance-p
        pair (cdr pairs)))
    nil))

(defun putnam-1964-a6-repeated-distance-hypothesis-p
    (remaining all-pairs probe)
  (if (consp remaining)
      (and
       (implies
        (putnam-1964-a6-has-longer-distance-p
         (car remaining) all-pairs probe)
        (putnam-1964-a6-has-other-equal-distance-p
         (car remaining) all-pairs))
       (putnam-1964-a6-repeated-distance-hypothesis-p
        (cdr remaining) all-pairs probe))
    t))

(defun putnam-1964-a6-first-nonzero-ratio
    (numerator denominator)
  (if (and (consp numerator) (consp denominator))
      (if (equal (car denominator) 0)
          (putnam-1964-a6-first-nonzero-ratio
           (cdr numerator) (cdr denominator))
        (cons (car numerator) (car denominator)))
    nil))

(defun putnam-1964-a6-proportional-with-pivot-p
    (numerator denominator pivot-numerator pivot-denominator)
  (if (and (consp numerator) (consp denominator))
      (and
       (equal
        (* (car numerator) pivot-denominator)
        (* (car denominator) pivot-numerator))
       (putnam-1964-a6-proportional-with-pivot-p
        (cdr numerator)
        (cdr denominator)
        pivot-numerator
        pivot-denominator))
    (and (equal numerator nil)
         (equal denominator nil))))

(defun putnam-1964-a6-rationally-proportional-p
    (numerator denominator)
  (let ((pivot
         (putnam-1964-a6-first-nonzero-ratio
          numerator denominator)))
    (and
     pivot
     (putnam-1964-a6-proportional-with-pivot-p
      numerator denominator (car pivot) (cdr pivot)))))

(defun putnam-1964-a6-ratios-from-pair-rational-p
    (pair pairs)
  (if (consp pairs)
      (and
       (implies
        (not (equal pair (car pairs)))
        (putnam-1964-a6-rationally-proportional-p
         (putnam-1964-a6-pair-distance pair)
         (putnam-1964-a6-pair-distance
          (car pairs))))
       (putnam-1964-a6-ratios-from-pair-rational-p
        pair (cdr pairs)))
    t))

(defun putnam-1964-a6-all-ratios-rational-p
    (remaining all-pairs)
  (if (consp remaining)
      (and
       (putnam-1964-a6-ratios-from-pair-rational-p
        (car remaining) all-pairs)
       (putnam-1964-a6-all-ratios-rational-p
        (cdr remaining) all-pairs))
    t))

(defun putnambench-putnam-1964-a6-statement
    (points probe)
  (implies
   (and
    (true-listp points)
    (true-listp probe)
    (putnam-1964-a6-rational-vector-p
     probe (len probe))
    (putnam-1964-a6-point-list-p
     points (len probe))
    (no-duplicatesp-equal points)
    (putnam-1964-a6-point-projections-distinct-p
     points probe))
   (let ((pairs
          (putnam-1964-a6-pairs points probe)))
     (implies
      (and
       (putnam-1964-a6-distance-projections-separated-p
        pairs probe)
       (putnam-1964-a6-repeated-distance-hypothesis-p
        pairs pairs probe))
      (putnam-1964-a6-all-ratios-rational-p
       pairs pairs)))))

(value-triple :itpeval-statement-checked)
:q
