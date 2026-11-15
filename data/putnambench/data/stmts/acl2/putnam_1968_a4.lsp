;; Statement-only formalization of PutnamBench artifact putnam_1968_a4:
;; the sum of squared distances over all unordered pairs among n points on
;; the unit sphere in real three-space is at most n^2. This file contains no
;; proof.

(in-package "ACL2")

;; A length-n list is definitionally equivalent to a function on Fin n.
;; ACL2 evaluates its coordinates over the rationals. This preserves the real
;; statement in both directions: rational unit-sphere points are real points,
;; while rational points are dense in the real unit sphere (for example by
;; stereographic parametrization). If a real n-tuple violated the bound, its
;; pairwise squared-distance sum would be strictly greater than n^2; continuity
;; on the finite product of spheres would then give a nearby rational
;; unit-sphere n-tuple with the same strict violation.

(defun putnam-1968-a4-rational-point-p (point)
  (and (true-listp point)
       (equal (len point) 3)
       (rationalp (nth 0 point))
       (rationalp (nth 1 point))
       (rationalp (nth 2 point))))

(defun putnam-1968-a4-rational-point-list-p (points)
  (if (consp points)
      (and (putnam-1968-a4-rational-point-p (car points))
           (putnam-1968-a4-rational-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1968-a4-square (x)
  (* x x))

(defun putnam-1968-a4-unit-point-p (point)
  (equal
   (+ (putnam-1968-a4-square (nth 0 point))
      (putnam-1968-a4-square (nth 1 point))
      (putnam-1968-a4-square (nth 2 point)))
   1))

(defun putnam-1968-a4-unit-point-list-p (points)
  (if (consp points)
      (and (putnam-1968-a4-unit-point-p (car points))
           (putnam-1968-a4-unit-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1968-a4-distance-squared (left right)
  (+ (putnam-1968-a4-square
      (- (nth 0 left) (nth 0 right)))
     (putnam-1968-a4-square
      (- (nth 1 left) (nth 1 right)))
     (putnam-1968-a4-square
      (- (nth 2 left) (nth 2 right)))))

(defun putnam-1968-a4-sum-from-point (point remaining)
  (if (consp remaining)
      (+ (putnam-1968-a4-distance-squared point (car remaining))
         (putnam-1968-a4-sum-from-point point (cdr remaining)))
    0))

(defun putnam-1968-a4-pairwise-sum (points)
  (if (consp points)
      (+ (putnam-1968-a4-sum-from-point
          (car points) (cdr points))
         (putnam-1968-a4-pairwise-sum (cdr points)))
    0))

(defun putnambench-putnam-1968-a4-statement (n points)
  (implies
   (and (natp n)
        (true-listp points)
        (equal (len points) n)
        (putnam-1968-a4-rational-point-list-p points)
        (putnam-1968-a4-unit-point-list-p points))
   (<= (putnam-1968-a4-pairwise-sum points)
       (* n n))))

(value-triple :itpeval-statement-checked)
:q
