;; Statement-only formalization of PutnamBench artifact putnam_1962_a1:
;; every five-point subset of the real plane in general position contains
;; four points that are the vertices of a convex quadrilateral. This file
;; contains no proof.

(in-package "ACL2")

;; A five-point real configuration in general position has only finitely many
;; nonzero orientation determinants. Coordinate-wise rational approximation
;; can therefore preserve all their signs. Conversely, rational configurations
;; are real configurations. Strict containment in a triangle, and hence the
;; convex-four conclusion below, depends only on these orientation signs.
;; Thus the universal rational-coordinate encoding is bidirectionally
;; equivalent to the source statement over arbitrary real coordinates.

(defun putnam-1962-a1-rational-point-p (point)
  (and (true-listp point)
       (equal (len point) 2)
       (rationalp (nth 0 point))
       (rationalp (nth 1 point))))

(defun putnam-1962-a1-rational-point-list-p (points)
  (if (consp points)
      (and (putnam-1962-a1-rational-point-p (car points))
           (putnam-1962-a1-rational-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1962-a1-orientation (a b c)
  (- (* (- (nth 0 b) (nth 0 a))
        (- (nth 1 c) (nth 1 a)))
     (* (- (nth 1 b) (nth 1 a))
        (- (nth 0 c) (nth 0 a)))))

(defun putnam-1962-a1-noncollinear-with-third-p
    (a b remaining)
  (if (consp remaining)
      (and
       (not (equal
             (putnam-1962-a1-orientation a b (car remaining))
             0))
       (putnam-1962-a1-noncollinear-with-third-p
        a b (cdr remaining)))
    t))

(defun putnam-1962-a1-noncollinear-with-pairs-p
    (a remaining)
  (if (consp remaining)
      (and
       (putnam-1962-a1-noncollinear-with-third-p
        a (car remaining) (cdr remaining))
       (putnam-1962-a1-noncollinear-with-pairs-p
        a (cdr remaining)))
    t))

(defun putnam-1962-a1-general-position-p (points)
  (if (consp points)
      (and
       (putnam-1962-a1-noncollinear-with-pairs-p
        (car points) (cdr points))
       (putnam-1962-a1-general-position-p (cdr points)))
    t))

(defun putnam-1962-a1-strictly-inside-triangle-p
    (point a b c)
  (let ((first
         (putnam-1962-a1-orientation a b point))
        (second
         (putnam-1962-a1-orientation b c point))
        (third
         (putnam-1962-a1-orientation c a point)))
    (or (and (< 0 first)
             (< 0 second)
             (< 0 third))
        (and (< first 0)
             (< second 0)
             (< third 0)))))

(defun putnam-1962-a1-convex-four-p (points)
  (and
   (true-listp points)
   (equal (len points) 4)
   (let ((first (nth 0 points))
         (second (nth 1 points))
         (third (nth 2 points))
         (fourth (nth 3 points)))
     (and
      (not
       (putnam-1962-a1-strictly-inside-triangle-p
        first second third fourth))
      (not
       (putnam-1962-a1-strictly-inside-triangle-p
        second first third fourth))
      (not
       (putnam-1962-a1-strictly-inside-triangle-p
        third first second fourth))
      (not
       (putnam-1962-a1-strictly-inside-triangle-p
        fourth first second third))))))

(defun putnam-1962-a1-some-convex-four-p
    (chosen remaining needed)
  (declare (xargs :measure (len remaining)))
  (cond
   ((zp needed)
    (putnam-1962-a1-convex-four-p chosen))
   ((endp remaining) nil)
   (t
    (or
     (putnam-1962-a1-some-convex-four-p
      (cons (car remaining) chosen)
      (cdr remaining)
      (- needed 1))
     (putnam-1962-a1-some-convex-four-p
      chosen
      (cdr remaining)
      needed)))))

(defun putnambench-putnam-1962-a1-statement (points)
  (implies
   (and
    (true-listp points)
    (equal (len points) 5)
    (putnam-1962-a1-rational-point-list-p points)
    (no-duplicatesp-equal points)
    (putnam-1962-a1-general-position-p points))
   (putnam-1962-a1-some-convex-four-p nil points 4)))

(value-triple :itpeval-statement-checked)
:q
