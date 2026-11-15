;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__092, "Pick's Theorem": the area of a simple closed
;; polygonal path with integer-coordinate vertices equals its number of
;; interior lattice points plus half its number of boundary lattice points
;; minus one. This file contains no proof.

(defun ht092-lattice-point-p (point)
  (and (true-listp point)
       (equal (len point) 2)
       (integerp (car point))
       (integerp (cadr point))))

(defun ht092-all-lattice-points-p (points)
  (if (consp points)
      (and (ht092-lattice-point-p (car points))
           (ht092-all-lattice-points-p (cdr points)))
    t))

(defun ht092-point-member-p (point points)
  (if (consp points)
      (or (equal point (car points))
          (ht092-point-member-p point (cdr points)))
    nil))

(defun ht092-distinct-points-p (points)
  (if (consp points)
      (and (not (ht092-point-member-p (car points) (cdr points)))
           (ht092-distinct-points-p (cdr points)))
    t))

(defun ht092-butlast-points (points)
  (if (or (not (consp points))
          (not (consp (cdr points))))
      nil
    (cons (car points)
          (ht092-butlast-points (cdr points)))))

(defun ht092-last-point (points)
  (if (not (consp points))
      nil
    (if (not (consp (cdr points)))
        (car points)
      (ht092-last-point (cdr points)))))

(defun ht092-x (point)
  (car point))

(defun ht092-y (point)
  (cadr point))

(defun ht092-min2 (x y)
  (if (< x y) x y))

(defun ht092-max2 (x y)
  (if (< x y) y x))

(defun ht092-orientation (a b c)
  (- (* (- (ht092-x b) (ht092-x a))
        (- (ht092-y c) (ht092-y a)))
     (* (- (ht092-y b) (ht092-y a))
        (- (ht092-x c) (ht092-x a)))))

(defun ht092-dot-from (origin a b)
  (+ (* (- (ht092-x a) (ht092-x origin))
        (- (ht092-x b) (ht092-x origin)))
     (* (- (ht092-y a) (ht092-y origin))
        (- (ht092-y b) (ht092-y origin)))))

(defun ht092-point-on-segment-p (point a b)
  (and (equal (ht092-orientation a b point) 0)
       (<= (ht092-min2 (ht092-x a) (ht092-x b))
           (ht092-x point))
       (<= (ht092-x point)
           (ht092-max2 (ht092-x a) (ht092-x b)))
       (<= (ht092-min2 (ht092-y a) (ht092-y b))
           (ht092-y point))
       (<= (ht092-y point)
           (ht092-max2 (ht092-y a) (ht092-y b)))))

(defun ht092-segments-intersect-p (a b c d)
  (and (<= (ht092-min2 (ht092-x a) (ht092-x b))
           (ht092-max2 (ht092-x c) (ht092-x d)))
       (<= (ht092-min2 (ht092-x c) (ht092-x d))
           (ht092-max2 (ht092-x a) (ht092-x b)))
       (<= (ht092-min2 (ht092-y a) (ht092-y b))
           (ht092-max2 (ht092-y c) (ht092-y d)))
       (<= (ht092-min2 (ht092-y c) (ht092-y d))
           (ht092-max2 (ht092-y a) (ht092-y b)))
       (<= (* (ht092-orientation a b c)
              (ht092-orientation a b d))
           0)
       (<= (* (ht092-orientation c d a)
              (ht092-orientation c d b))
           0)))

(defun ht092-common-endpoint-count (a b c d)
  (+ (if (equal a c) 1 0)
     (if (equal a d) 1 0)
     (if (equal b c) 1 0)
     (if (equal b d) 1 0)))

(defun ht092-shared-endpoint-is-only-meeting-p (shared a b)
  (or (not (equal (ht092-orientation shared a b) 0))
      (< (ht092-dot-from shared a b) 0)))

(defun ht092-edge-pair-simple-p (edge1 edge2)
  (let* ((a (car edge1))
         (b (cadr edge1))
         (c (car edge2))
         (d (cadr edge2))
         (common (ht092-common-endpoint-count a b c d)))
    (cond ((equal common 0)
           (not (ht092-segments-intersect-p a b c d)))
          ((not (equal common 1))
           nil)
          ((equal a c)
           (ht092-shared-endpoint-is-only-meeting-p a b d))
          ((equal a d)
           (ht092-shared-endpoint-is-only-meeting-p a b c))
          ((equal b c)
           (ht092-shared-endpoint-is-only-meeting-p b a d))
          (t
           (ht092-shared-endpoint-is-only-meeting-p b a c)))))

(defun ht092-edges (vertices)
  (if (and (consp vertices)
           (consp (cdr vertices)))
      (cons (list (car vertices) (cadr vertices))
            (ht092-edges (cdr vertices)))
    nil))

(defun ht092-edge-compatible-with-all-p (edge edges)
  (if (consp edges)
      (and (ht092-edge-pair-simple-p edge (car edges))
           (ht092-edge-compatible-with-all-p edge (cdr edges)))
    t))

(defun ht092-all-edge-pairs-simple-p (edges)
  (if (consp edges)
      (and (ht092-edge-compatible-with-all-p (car edges) (cdr edges))
           (ht092-all-edge-pairs-simple-p (cdr edges)))
    t))

(defun ht092-simple-closed-lattice-polygon-p (vertices)
  (and (true-listp vertices)
       (<= 4 (len vertices))
       (ht092-all-lattice-points-p vertices)
       (equal (car vertices) (ht092-last-point vertices))
       (ht092-distinct-points-p (ht092-butlast-points vertices))
       (ht092-all-edge-pairs-simple-p (ht092-edges vertices))))

(defun ht092-point-on-any-edge-p (point edges)
  (if (consp edges)
      (or (ht092-point-on-segment-p point
                                    (car (car edges))
                                    (cadr (car edges)))
          (ht092-point-on-any-edge-p point (cdr edges)))
    nil))

(defun ht092-edge-crosses-right-ray-p (point edge)
  (let* ((a (car edge))
         (b (cadr edge))
         (py (ht092-y point))
         (ay (ht092-y a))
         (by (ht092-y b))
         (side (ht092-orientation a b point)))
    (or (and (<= ay py)
             (< py by)
             (< 0 side))
        (and (<= by py)
             (< py ay)
             (< side 0)))))

(defun ht092-odd-ray-crossing-p (point edges)
  (if (consp edges)
      (let ((rest-is-odd
             (ht092-odd-ray-crossing-p point (cdr edges))))
        (if (ht092-edge-crosses-right-ray-p point (car edges))
            (not rest-is-odd)
          rest-is-odd))
    nil))

(defun ht092-interior-point-p (point edges)
  (and (not (ht092-point-on-any-edge-p point edges))
       (ht092-odd-ray-crossing-p point edges)))

(defun ht092-shoelace-sum (vertices)
  (if (and (consp vertices)
           (consp (cdr vertices)))
      (+ (- (* (ht092-x (car vertices))
               (ht092-y (cadr vertices)))
            (* (ht092-y (car vertices))
               (ht092-x (cadr vertices))))
         (ht092-shoelace-sum (cdr vertices)))
    0))

(defun ht092-abs (x)
  (if (< x 0) (- x) x))

(defun ht092-polygon-area (vertices)
  (/ (ht092-abs (ht092-shoelace-sum vertices)) 2))

(defun ht092-min-x (points)
  (if (not (consp (cdr points)))
      (ht092-x (car points))
    (ht092-min2 (ht092-x (car points))
                (ht092-min-x (cdr points)))))

(defun ht092-max-x (points)
  (if (not (consp (cdr points)))
      (ht092-x (car points))
    (ht092-max2 (ht092-x (car points))
                (ht092-max-x (cdr points)))))

(defun ht092-min-y (points)
  (if (not (consp (cdr points)))
      (ht092-y (car points))
    (ht092-min2 (ht092-y (car points))
                (ht092-min-y (cdr points)))))

(defun ht092-max-y (points)
  (if (not (consp (cdr points)))
      (ht092-y (car points))
    (ht092-max2 (ht092-y (car points))
                (ht092-max-y (cdr points)))))

(defun ht092-count-row (x y remaining-y edges boundaryp)
  (declare (xargs :measure (nfix remaining-y)))
  (if (zp remaining-y)
      0
    (+ (if (if boundaryp
               (ht092-point-on-any-edge-p (list x y) edges)
             (ht092-interior-point-p (list x y) edges))
           1
         0)
       (ht092-count-row x
                        (+ y 1)
                        (- remaining-y 1)
                        edges
                        boundaryp))))

(defun ht092-count-grid (x remaining-x min-y height edges boundaryp)
  (declare (xargs :measure (nfix remaining-x)))
  (if (zp remaining-x)
      0
    (+ (ht092-count-row x min-y height edges boundaryp)
       (ht092-count-grid (+ x 1)
                         (- remaining-x 1)
                         min-y
                         height
                         edges
                         boundaryp))))

(defun ht092-lattice-count (vertices boundaryp)
  (let* ((min-x (ht092-min-x vertices))
         (max-x (ht092-max-x vertices))
         (min-y (ht092-min-y vertices))
         (max-y (ht092-max-y vertices))
         (width (+ 1 (- max-x min-x)))
         (height (+ 1 (- max-y min-y)))
         (edges (ht092-edges vertices)))
    (ht092-count-grid min-x width min-y height edges boundaryp)))

(defun ht092-interior-lattice-count (vertices)
  (ht092-lattice-count vertices nil))

(defun ht092-boundary-lattice-count (vertices)
  (ht092-lattice-count vertices t))

(defun hundred-theorems-acl2-092-pick-s-theorem (vertices)
  (implies
   (ht092-simple-closed-lattice-polygon-p vertices)
   (equal
    (ht092-polygon-area vertices)
    (- (+ (ht092-interior-lattice-count vertices)
          (/ (ht092-boundary-lattice-count vertices) 2))
       1))))

(value-triple :itpeval-statement-checked)

:q
