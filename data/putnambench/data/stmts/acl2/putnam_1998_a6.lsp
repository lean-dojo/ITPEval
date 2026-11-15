;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_a6:
;; three distinct lattice points satisfying the stated perimeter-area
;; inequality are three vertices of a square. This file contains no proof.

(in-package "ACL2")

;; The source's integer-coordinate hypotheses identify A, B, and C
;; bijectively with the six integer coordinates used below. If U and V are
;; the squared lengths AB^2 and BC^2, and DELTA is the absolute orientation
;; determinant (twice the triangle area), then the source inequality is
;;
;;   U + V + 2*sqrt(U*V) < 4*DELTA + 1.
;;
;; With GAP = 4*DELTA + 1 - U - V and U,V >= 0, this is equivalent in both
;; directions to GAP > 0 and 4*U*V < GAP^2. Thus the predicate below uses
;; exact integer arithmetic without restricting or approximating the source
;; real inequality. Equal distances are likewise equivalent to equal squared
;; distances, and the source's threesquare predicate is unfolded definitionally.

(defun putnam-1998-a6-square (x)
  (* x x))

(defun putnam-1998-a6-distance-squared (left right)
  (+ (putnam-1998-a6-square
      (- (nth 0 left) (nth 0 right)))
     (putnam-1998-a6-square
      (- (nth 1 left) (nth 1 right)))))

(defun putnam-1998-a6-dot-at (left vertex right)
  (+ (* (- (nth 0 left) (nth 0 vertex))
        (- (nth 0 right) (nth 0 vertex)))
     (* (- (nth 1 left) (nth 1 vertex))
        (- (nth 1 right) (nth 1 vertex)))))

(defun putnam-1998-a6-orientation (a b c)
  (- (* (- (nth 0 b) (nth 0 a))
        (- (nth 1 c) (nth 1 a)))
     (* (- (nth 1 b) (nth 1 a))
        (- (nth 0 c) (nth 0 a)))))

(defun putnam-1998-a6-area-bound-p (a b c)
  (let* ((u (putnam-1998-a6-distance-squared a b))
         (v (putnam-1998-a6-distance-squared b c))
         (twice-area
          (abs (putnam-1998-a6-orientation a b c)))
         (gap (- (- (+ (* 4 twice-area) 1) u) v)))
    (and
     (< 0 gap)
     (< (* 4 u v)
        (putnam-1998-a6-square gap)))))

(defun putnam-1998-a6-three-square-p (left vertex right)
  (and
   (equal
    (putnam-1998-a6-distance-squared vertex left)
    (putnam-1998-a6-distance-squared vertex right))
   (equal (putnam-1998-a6-dot-at left vertex right) 0)))

(defun putnambench-putnam-1998-a6-statement
    (a-x a-y b-x b-y c-x c-y)
  (let ((a (list a-x a-y))
        (b (list b-x b-y))
        (c (list c-x c-y)))
    (implies
     (and
      (integerp a-x)
      (integerp a-y)
      (integerp b-x)
      (integerp b-y)
      (integerp c-x)
      (integerp c-y)
      (not (equal a b))
      (not (equal a c))
      (not (equal b c))
      (putnam-1998-a6-area-bound-p a b c))
     (or
      (putnam-1998-a6-three-square-p a b c)
      (putnam-1998-a6-three-square-p b c a)
      (putnam-1998-a6-three-square-p c a b)))))

(value-triple :itpeval-statement-checked)
:q
