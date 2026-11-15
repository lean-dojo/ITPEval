;; Statement-only formalization of PutnamBench artifact putnam_1964_b4:
;; the number of spherical regions cut out by finitely many great circles in
;; general position is n^2-n+2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A duplicate-free family of great circles is represented by a true list of
;; nonzero normal vectors. Two normals define the same great circle exactly
;; when they are parallel, and three great circles have a common antipodal
;; pair exactly when their normals have zero determinant. Thus the pairwise
;; nonparallel and nonzero-determinant tests below are the source injectivity
;; and general-position assumptions.
;;
;; The source definition of IsRegion identifies its nonempty regions
;; bijectively with sign vectors for which some point has all prescribed
;; nonzero dot-product signs. A nonzero point with those signs can be
;; normalized onto the unit sphere, so feasibility is exactly feasibility of
;; the corresponding strict homogeneous linear inequalities.
;; Fourier-Motzkin elimination decides that feasibility without bounding or
;; sampling the sphere, and the recursive two-way branch ranges over every
;; sign vector.
;;
;; ACL2 evaluates the displayed vectors over the rationals. This is
;; bidirectionally equivalent to the real statement under general position:
;; every rational instance is real, while any finite real normal family can
;; be approximated by rational normals without changing its nonzero cross
;; products, determinant signs, oriented matroid, or feasible sign vectors.
;; Hence neither the real domain nor the arbitrary circle family is narrowed
;; by this representation.

(defun putnam-1964-b4-rational-vector3-p (vector)
  (and (true-listp vector)
       (equal (len vector) 3)
       (rationalp (nth 0 vector))
       (rationalp (nth 1 vector))
       (rationalp (nth 2 vector))))

(defun putnam-1964-b4-vector-list-p (vectors)
  (if (consp vectors)
      (and (putnam-1964-b4-rational-vector3-p (car vectors))
           (putnam-1964-b4-vector-list-p (cdr vectors)))
    (equal vectors nil)))

(defun putnam-1964-b4-zero-vector-p (vector)
  (and (equal (nth 0 vector) 0)
       (equal (nth 1 vector) 0)
       (equal (nth 2 vector) 0)))

(defun putnam-1964-b4-all-nonzero-p (vectors)
  (if (consp vectors)
      (and (not (putnam-1964-b4-zero-vector-p (car vectors)))
           (putnam-1964-b4-all-nonzero-p (cdr vectors)))
    t))

(defun putnam-1964-b4-cross-product (left right)
  (list
   (- (* (nth 1 left) (nth 2 right))
      (* (nth 2 left) (nth 1 right)))
   (- (* (nth 2 left) (nth 0 right))
      (* (nth 0 left) (nth 2 right)))
   (- (* (nth 0 left) (nth 1 right))
      (* (nth 1 left) (nth 0 right)))))

(defun putnam-1964-b4-nonparallel-with-p (vector remaining)
  (if (consp remaining)
      (and
       (not
        (putnam-1964-b4-zero-vector-p
         (putnam-1964-b4-cross-product vector (car remaining))))
       (putnam-1964-b4-nonparallel-with-p
        vector (cdr remaining)))
    t))

(defun putnam-1964-b4-pairwise-nonparallel-p (vectors)
  (if (consp vectors)
      (and
       (putnam-1964-b4-nonparallel-with-p
        (car vectors) (cdr vectors))
       (putnam-1964-b4-pairwise-nonparallel-p (cdr vectors)))
    t))

(defun putnam-1964-b4-determinant3 (first second third)
  (+
   (* (nth 0 first)
      (- (* (nth 1 second) (nth 2 third))
         (* (nth 2 second) (nth 1 third))))
   (-
    (* (nth 1 first)
       (- (* (nth 0 second) (nth 2 third))
          (* (nth 2 second) (nth 0 third)))))
   (* (nth 2 first)
      (- (* (nth 0 second) (nth 1 third))
         (* (nth 1 second) (nth 0 third))))))

(defun putnam-1964-b4-independent-with-third-p
    (first second remaining)
  (if (consp remaining)
      (and
       (not
        (equal
         (putnam-1964-b4-determinant3
          first second (car remaining))
         0))
       (putnam-1964-b4-independent-with-third-p
        first second (cdr remaining)))
    t))

(defun putnam-1964-b4-independent-with-pairs-p
    (first remaining)
  (if (consp remaining)
      (and
       (putnam-1964-b4-independent-with-third-p
        first (car remaining) (cdr remaining))
       (putnam-1964-b4-independent-with-pairs-p
        first (cdr remaining)))
    t))

(defun putnam-1964-b4-general-position-p (vectors)
  (if (consp vectors)
      (and
       (putnam-1964-b4-independent-with-pairs-p
        (car vectors) (cdr vectors))
       (putnam-1964-b4-general-position-p (cdr vectors)))
    t))

(defun putnam-1964-b4-vector-negate (vector)
  (if (consp vector)
      (cons (- (car vector))
            (putnam-1964-b4-vector-negate (cdr vector)))
    nil))

;; For inequalities
;;
;;   p*x + P > 0,  with p > 0,
;;   n*x + N > 0,  with n < 0,
;;
;; eliminating x gives p*N - n*P > 0.
(defun putnam-1964-b4-fm-combine-tails
    (positive-leading negative-tail negative-leading positive-tail)
  (if (and (consp negative-tail) (consp positive-tail))
      (cons
       (- (* positive-leading (car negative-tail))
          (* negative-leading (car positive-tail)))
       (putnam-1964-b4-fm-combine-tails
        positive-leading
        (cdr negative-tail)
        negative-leading
        (cdr positive-tail)))
    nil))

(defun putnam-1964-b4-fm-positive-inequalities (inequalities)
  (if (consp inequalities)
      (if (< 0 (caar inequalities))
          (cons (car inequalities)
                (putnam-1964-b4-fm-positive-inequalities
                 (cdr inequalities)))
        (putnam-1964-b4-fm-positive-inequalities
         (cdr inequalities)))
    nil))

(defun putnam-1964-b4-fm-negative-inequalities (inequalities)
  (if (consp inequalities)
      (if (< (caar inequalities) 0)
          (cons (car inequalities)
                (putnam-1964-b4-fm-negative-inequalities
                 (cdr inequalities)))
        (putnam-1964-b4-fm-negative-inequalities
         (cdr inequalities)))
    nil))

(defun putnam-1964-b4-fm-zero-tails (inequalities)
  (if (consp inequalities)
      (if (equal (caar inequalities) 0)
          (cons (cdar inequalities)
                (putnam-1964-b4-fm-zero-tails
                 (cdr inequalities)))
        (putnam-1964-b4-fm-zero-tails
         (cdr inequalities)))
    nil))

(defun putnam-1964-b4-fm-combine-with-negatives
    (positive negatives)
  (if (consp negatives)
      (cons
       (putnam-1964-b4-fm-combine-tails
        (car positive)
        (cdar negatives)
        (caar negatives)
        (cdr positive))
       (putnam-1964-b4-fm-combine-with-negatives
        positive (cdr negatives)))
    nil))

(defun putnam-1964-b4-fm-combine-all
    (positives negatives)
  (if (consp positives)
      (append
       (putnam-1964-b4-fm-combine-with-negatives
        (car positives) negatives)
       (putnam-1964-b4-fm-combine-all
        (cdr positives) negatives))
    nil))

(defun putnam-1964-b4-fm-eliminate-first (inequalities)
  (let ((positives
         (putnam-1964-b4-fm-positive-inequalities inequalities))
        (negatives
         (putnam-1964-b4-fm-negative-inequalities inequalities)))
    (append
     (putnam-1964-b4-fm-zero-tails inequalities)
     (putnam-1964-b4-fm-combine-all positives negatives))))

(defun putnam-1964-b4-strict-system-feasible-p
    (inequalities dimensions)
  (declare (xargs :measure (nfix dimensions)))
  (if (zp dimensions)
      (endp inequalities)
    (putnam-1964-b4-strict-system-feasible-p
     (putnam-1964-b4-fm-eliminate-first inequalities)
     (- dimensions 1))))

(defun putnam-1964-b4-count-feasible-signs
    (remaining signed-normals)
  (declare (xargs :measure (len remaining)))
  (if (consp remaining)
      (+
       (putnam-1964-b4-count-feasible-signs
        (cdr remaining)
        (cons (car remaining) signed-normals))
       (putnam-1964-b4-count-feasible-signs
        (cdr remaining)
        (cons
         (putnam-1964-b4-vector-negate (car remaining))
         signed-normals)))
    (if
        (putnam-1964-b4-strict-system-feasible-p
         signed-normals 3)
        1
      0)))

(defun putnambench-putnam-1964-b4-statement (normals)
  (implies
   (and
    (true-listp normals)
    (consp normals)
    (putnam-1964-b4-vector-list-p normals)
    (putnam-1964-b4-all-nonzero-p normals)
    (putnam-1964-b4-pairwise-nonparallel-p normals)
    (putnam-1964-b4-general-position-p normals))
   (let ((n (len normals)))
     (equal
      (putnam-1964-b4-count-feasible-signs normals nil)
      (+ (- (* n n) n) 2)))))

(value-triple :itpeval-statement-checked)
:q
