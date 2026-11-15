;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_b4:
;; every continuous plane curve of Euclidean length 1 is covered by a closed
;; rectangle of area 1/4. This file contains no proof.

(in-package "ACL2")

;; A code is an ordered rational polygonal path.  LENGTHS records the positive
;; rational Euclidean length of each consecutive segment, so the squared
;; distance equation below is exact and their sum being 1 is exactly the
;; source variation hypothesis for the associated piecewise-linear curve.
;;
;; This polygonal formulation is bidirectionally counterexample-preserving.
;; Every code denotes a source curve.  Conversely, failure of the source
;; conclusion means that the minimum area of an enclosing rectangle is
;; strictly greater than 1/4: any rectangle of smaller area can be widened to
;; area exactly 1/4.  Fine polygonal approximation preserves that strict
;; failure.  Rational unit directions and rational positive segment lengths
;; are dense; after approximating the segments, rational rescaling makes their
;; total length exactly 1 while preserving the strict failure.
;;
;; For a polygon, a minimum-area enclosing rectangle has a side parallel to an
;; edge of its convex hull.  Every hull edge joins two listed vertices.  For a
;; vertex-pair direction d, the rectangle side lengths are the spans of dot
;; and perpendicular projections divided by |d|, so its area is at most 1/4
;; exactly when
;;
;;   4 * dot-span * perpendicular-span <= |d|^2.
;;
;; The finite pair search therefore keeps the source rectangle existential
;; internal.  Its two projection slabs form a closed right-angled rectangle
;; covering every segment, and widening a side gives area exactly 1/4.

(defun putnam-1969-b4-rational-point-p (point)
  (and (consp point)
       (rationalp (car point))
       (rationalp (cdr point))))

(defun putnam-1969-b4-distance-squared (left right)
  (+ (* (- (car right) (car left))
        (- (car right) (car left)))
     (* (- (cdr right) (cdr left))
        (- (cdr right) (cdr left)))))

(defun putnam-1969-b4-polygon-code-p (points lengths)
  (if (consp points)
      (if (consp (cdr points))
          (and (putnam-1969-b4-rational-point-p (car points))
               (consp lengths)
               (rationalp (car lengths))
               (< 0 (car lengths))
               (equal
                (putnam-1969-b4-distance-squared
                 (car points) (cadr points))
                (* (car lengths) (car lengths)))
               (putnam-1969-b4-polygon-code-p
                (cdr points) (cdr lengths)))
        (and (putnam-1969-b4-rational-point-p (car points))
             (equal (cdr points) nil)
             (equal lengths nil)))
    nil))

(defun putnam-1969-b4-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-1969-b4-sum (cdr values)))
    0))

(defun putnam-1969-b4-dot-projection (point dx dy)
  (+ (* (car point) dx)
     (* (cdr point) dy)))

(defun putnam-1969-b4-perpendicular-projection (point dx dy)
  (- (* (cdr point) dx)
     (* (car point) dy)))

(defun putnam-1969-b4-dot-min (points dx dy current)
  (if (consp points)
      (let ((value
             (putnam-1969-b4-dot-projection
              (car points) dx dy)))
        (putnam-1969-b4-dot-min
         (cdr points) dx dy
         (if (< value current) value current)))
    current))

(defun putnam-1969-b4-dot-max (points dx dy current)
  (if (consp points)
      (let ((value
             (putnam-1969-b4-dot-projection
              (car points) dx dy)))
        (putnam-1969-b4-dot-max
         (cdr points) dx dy
         (if (< current value) value current)))
    current))

(defun putnam-1969-b4-perpendicular-min
    (points dx dy current)
  (if (consp points)
      (let ((value
             (putnam-1969-b4-perpendicular-projection
              (car points) dx dy)))
        (putnam-1969-b4-perpendicular-min
         (cdr points) dx dy
         (if (< value current) value current)))
    current))

(defun putnam-1969-b4-perpendicular-max
    (points dx dy current)
  (if (consp points)
      (let ((value
             (putnam-1969-b4-perpendicular-projection
              (car points) dx dy)))
        (putnam-1969-b4-perpendicular-max
         (cdr points) dx dy
         (if (< current value) value current)))
    current))

(defun putnam-1969-b4-quarter-area-direction-p
    (left right all-points)
  (let* ((dx (- (car right) (car left)))
         (dy (- (cdr right) (cdr left)))
         (norm-squared (+ (* dx dx) (* dy dy)))
         (first (car all-points))
         (first-dot
          (putnam-1969-b4-dot-projection first dx dy))
         (first-perpendicular
          (putnam-1969-b4-perpendicular-projection first dx dy))
         (dot-span
          (- (putnam-1969-b4-dot-max
              (cdr all-points) dx dy first-dot)
             (putnam-1969-b4-dot-min
              (cdr all-points) dx dy first-dot)))
         (perpendicular-span
          (- (putnam-1969-b4-perpendicular-max
              (cdr all-points) dx dy first-perpendicular)
             (putnam-1969-b4-perpendicular-min
              (cdr all-points) dx dy first-perpendicular))))
    (and (< 0 norm-squared)
         (<= (* 4 dot-span perpendicular-span)
             norm-squared))))

(defun putnam-1969-b4-direction-from-point-p
    (left remaining all-points)
  (if (consp remaining)
      (or (putnam-1969-b4-quarter-area-direction-p
           left (car remaining) all-points)
          (putnam-1969-b4-direction-from-point-p
           left (cdr remaining) all-points))
    nil))

(defun putnam-1969-b4-enclosing-quarter-rectangle-p
    (remaining all-points)
  (if (consp remaining)
      (or (putnam-1969-b4-direction-from-point-p
           (car remaining) (cdr remaining) all-points)
          (putnam-1969-b4-enclosing-quarter-rectangle-p
           (cdr remaining) all-points))
    nil))

(defun putnambench-putnam-1969-b4-statement (points lengths)
  (implies
   (and (true-listp points)
        (true-listp lengths)
        (consp (cdr points))
        (putnam-1969-b4-polygon-code-p points lengths)
        (equal (putnam-1969-b4-sum lengths) 1))
   (putnam-1969-b4-enclosing-quarter-rectangle-p
    points points)))

(value-triple :itpeval-statement-checked)
:q
