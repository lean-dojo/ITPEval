;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_a6:
;; positivity of the prescribed integer-lattice weight double sum for every
;; finite nonempty subset of Z x Z. This file contains no proof.

(in-package "ACL2")

;; The source hypotheses uniquely determine W at every integer pair and A on
;; every finite set, so both functions are unfolded below. A duplicate-free
;; true list of two-integer lists is a bijective enumeration of a finite subset
;; of Z x Z, and the double sum is invariant under the enumeration order.

(defun putnam-2013-a6-integer-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (integerp (nth 0 point))
   (integerp (nth 1 point))))

(defun putnam-2013-a6-all-integer-points-p (points)
  (if (endp points)
      (equal points nil)
    (and
     (putnam-2013-a6-integer-point-p (car points))
     (putnam-2013-a6-all-integer-points-p (cdr points)))))

(defun putnam-2013-a6-weight (a b)
  (let ((x (abs a))
        (y (abs b)))
    (cond
     ((or (< 2 x) (< 2 y)) 0)
     ((and (equal x 2) (equal y 2)) -1)
     ((or (and (equal x 2) (equal y 1))
          (and (equal x 1) (equal y 2)))
      -2)
     ((or (and (equal x 2) (equal y 0))
          (and (equal x 0) (equal y 2)))
      2)
     ((and (equal x 1) (equal y 1)) 4)
     ((or (and (equal x 1) (equal y 0))
          (and (equal x 0) (equal y 1)))
      -4)
     (t 12))))

(defun putnam-2013-a6-row-sum (point others)
  (if (endp others)
      0
    (+
     (putnam-2013-a6-weight
      (- (nth 0 point) (nth 0 (car others)))
      (- (nth 1 point) (nth 1 (car others))))
     (putnam-2013-a6-row-sum point (cdr others)))))

(defun putnam-2013-a6-double-sum (remaining all-points)
  (if (endp remaining)
      0
    (+
     (putnam-2013-a6-row-sum (car remaining) all-points)
     (putnam-2013-a6-double-sum
      (cdr remaining) all-points))))

(defun putnambench-putnam-2013-a6-statement (points)
  (implies
   (and
    (true-listp points)
    (consp points)
    (no-duplicatesp-equal points)
    (putnam-2013-a6-all-integer-points-p points))
   (< 0
      (putnam-2013-a6-double-sum points points))))

(value-triple :itpeval-statement-checked)
:q
