;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_a4:
;; every finite balanced red-blue set of real-plane points in general position
;; admits a red-blue perfect matching by pairwise disjoint closed straight line
;; segments. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A counterexample contains only finitely many points, and every orientation
;; determinant of three of them is nonzero. Rational points can be chosen
;; sufficiently close to all source points that every one of those finitely
;; many determinant signs is preserved. For four distinct points in general
;; position, two closed segments intersect exactly when their endpoint
;; orientation signs are opposite in both directions. The perturbation
;; therefore preserves every possible red-blue segment intersection and hence
;; preserves whether a nonintersecting perfect matching exists. Conversely,
;; every rational configuration below is a real source configuration. Thus
;; the rational encoding is bidirectionally equivalent to the arbitrary-real
;; statement and does not restrict its generality.

(defun putnam-1979-a4-rational-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (rationalp (nth 0 point))
   (rationalp (nth 1 point))))

(defun putnam-1979-a4-rational-point-list-p (points)
  (if (consp points)
      (and
       (putnam-1979-a4-rational-point-p (car points))
       (putnam-1979-a4-rational-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1979-a4-disjoint-point-lists-p (left right)
  (if (consp left)
      (and
       (not (member-equal (car left) right))
       (putnam-1979-a4-disjoint-point-lists-p
        (cdr left) right))
    t))

(defun putnam-1979-a4-orientation (a b c)
  (-
   (* (- (nth 0 b) (nth 0 a))
      (- (nth 1 c) (nth 1 a)))
   (* (- (nth 1 b) (nth 1 a))
      (- (nth 0 c) (nth 0 a)))))

(defun putnam-1979-a4-noncollinear-with-third-p
    (a b remaining)
  (if (consp remaining)
      (and
       (not
        (equal
         (putnam-1979-a4-orientation
          a b (car remaining))
         0))
       (putnam-1979-a4-noncollinear-with-third-p
        a b (cdr remaining)))
    t))

(defun putnam-1979-a4-noncollinear-with-pairs-p
    (a remaining)
  (if (consp remaining)
      (and
       (putnam-1979-a4-noncollinear-with-third-p
        a (car remaining) (cdr remaining))
       (putnam-1979-a4-noncollinear-with-pairs-p
        a (cdr remaining)))
    t))

(defun putnam-1979-a4-general-position-p (points)
  (if (consp points)
      (and
       (putnam-1979-a4-noncollinear-with-pairs-p
        (car points) (cdr points))
       (putnam-1979-a4-general-position-p (cdr points)))
    t))

(defun putnam-1979-a4-opposite-signs-p (left right)
  (or
   (and (< left 0) (< 0 right))
   (and (< right 0) (< 0 left))))

(defun putnam-1979-a4-segments-intersect-p (first second)
  (let ((a (nth 0 first))
        (b (nth 1 first))
        (c (nth 0 second))
        (d (nth 1 second)))
    (and
     (putnam-1979-a4-opposite-signs-p
      (putnam-1979-a4-orientation a b c)
      (putnam-1979-a4-orientation a b d))
     (putnam-1979-a4-opposite-signs-p
      (putnam-1979-a4-orientation c d a)
      (putnam-1979-a4-orientation c d b)))))

(defun putnam-1979-a4-segment-disjoint-from-list-p
    (segment segments)
  (if (consp segments)
      (and
       (not
        (putnam-1979-a4-segments-intersect-p
         segment (car segments)))
       (putnam-1979-a4-segment-disjoint-from-list-p
        segment (cdr segments)))
    t))

;; This finite branching search is the source's internal existential
;; quantifier over perfect red-blue matchings. At each red point it tries
;; every remaining blue point, removing the selected point before continuing.
;; The fuel exceeds the maximum number of candidate scans along any branch.

(defun putnam-1979-a4-matching-search-p
    (fuel reds blues candidates segments)
  (declare (xargs :measure (nfix fuel)))
  (cond
   ((endp reds) t)
   ((or (zp fuel) (endp candidates)) nil)
   (t
    (let* ((blue (car candidates))
           (segment (list (car reds) blue)))
      (or
       (and
        (putnam-1979-a4-segment-disjoint-from-list-p
         segment segments)
        (putnam-1979-a4-matching-search-p
         (- fuel 1)
         (cdr reds)
         (remove-equal blue blues)
         (remove-equal blue blues)
         (cons segment segments)))
       (putnam-1979-a4-matching-search-p
        (- fuel 1)
        reds
        blues
        (cdr candidates)
        segments))))))

(defun putnam-1979-a4-matching-exists-p (reds blues)
  (let ((cardinality (len reds)))
    (if (zp cardinality)
        t
      (putnam-1979-a4-matching-search-p
       (+ 1 (* cardinality (+ cardinality 1)))
       reds
       blues
       blues
       nil))))

(defun putnambench-putnam-1979-a4-statement (reds blues)
  (implies
   (and
    (true-listp reds)
    (true-listp blues)
    (putnam-1979-a4-rational-point-list-p reds)
    (putnam-1979-a4-rational-point-list-p blues)
    (equal (len reds) (len blues))
    (no-duplicatesp-equal reds)
    (no-duplicatesp-equal blues)
    (putnam-1979-a4-disjoint-point-lists-p reds blues)
    (putnam-1979-a4-general-position-p (append reds blues)))
   (putnam-1979-a4-matching-exists-p reds blues)))

(value-triple :itpeval-statement-checked)
:q
