;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_a1:
;; area inequalities for a triangle and three points on its closed sides.
;; This file contains no proof.

(in-package "ACL2")

;; Closed-segment membership is expressed by collinearity together with
;; (P-L) dot (P-R) <= 0. Squared distances preserve the source distance
;; comparisons, and absolute orientation determinants are twice the triangle
;; areas, so their common factor cancels from every area comparison. The
;; infimum of the three corner-triangle areas is at most the central area
;; exactly when at least one of those three areas is at most the central area.
;;
;; ACL2 evaluates the coordinates below as exact rationals. This universal
;; rational-coordinate statement is bidirectionally equivalent to the source
;; statement over arbitrary real coordinates. Every rational configuration is
;; real. Conversely, in any real counterexample the noncollinear vertices make
;; the three side parameters unique. Approximate the vertices and parameters
;; by rationals, keeping each parameter in [0,1] and, when required, in
;; [0,1/2], and reconstruct the side points. Noncollinearity persists. Failure
;; of either conclusion is given by strict area inequalities, so it also
;; persists under a sufficiently close approximation. Thus every real
;; counterexample would yield a rational counterexample.

(defun putnam-1973-a1-orientation (a b c)
  (- (* (- (car b) (car a))
        (- (cadr c) (cadr a)))
     (* (- (cadr b) (cadr a))
        (- (car c) (car a)))))

(defun putnam-1973-a1-vector-dot-from (point left right)
  (+ (* (- (car point) (car left))
        (- (car point) (car right)))
     (* (- (cadr point) (cadr left))
        (- (cadr point) (cadr right)))))

(defun putnam-1973-a1-on-closed-segment-p (point left right)
  (and
   (equal (putnam-1973-a1-orientation left right point) 0)
   (<= (putnam-1973-a1-vector-dot-from point left right) 0)))

(defun putnam-1973-a1-distance-squared (left right)
  (+ (* (- (car left) (car right))
        (- (car left) (car right)))
     (* (- (cadr left) (cadr right))
        (- (cadr left) (cadr right)))))

(defun putnam-1973-a1-absolute (value)
  (if (< value 0) (- value) value))

(defun putnam-1973-a1-twice-area (a b c)
  (putnam-1973-a1-absolute
   (putnam-1973-a1-orientation a b c)))

(defun putnambench-putnam-1973-a1-statement
    (a-x a-y b-x b-y c-x c-y x-x x-y y-x y-y z-x z-y)
  (let ((a (list a-x a-y))
        (b (list b-x b-y))
        (c (list c-x c-y))
        (x (list x-x x-y))
        (y (list y-x y-y))
        (z (list z-x z-y)))
    (implies
     (and
      (rationalp a-x) (rationalp a-y)
      (rationalp b-x) (rationalp b-y)
      (rationalp c-x) (rationalp c-y)
      (rationalp x-x) (rationalp x-y)
      (rationalp y-x) (rationalp y-y)
      (rationalp z-x) (rationalp z-y)
      (not (equal (putnam-1973-a1-orientation a b c) 0))
      (putnam-1973-a1-on-closed-segment-p x b c)
      (putnam-1973-a1-on-closed-segment-p y c a)
      (putnam-1973-a1-on-closed-segment-p z a b))
     (let ((abc-area (putnam-1973-a1-twice-area a b c))
           (xyz-area (putnam-1973-a1-twice-area x y z))
           (azy-area (putnam-1973-a1-twice-area a z y))
           (bxz-area (putnam-1973-a1-twice-area b x z))
           (cyx-area (putnam-1973-a1-twice-area c y x)))
       (and
        (implies
         (and
          (<= (putnam-1973-a1-distance-squared b x)
              (putnam-1973-a1-distance-squared x c))
          (<= (putnam-1973-a1-distance-squared c y)
              (putnam-1973-a1-distance-squared y a))
          (<= (putnam-1973-a1-distance-squared a z)
              (putnam-1973-a1-distance-squared z b)))
         (<= (* (/ 1 4) abc-area) xyz-area))
        (or
         (<= azy-area xyz-area)
         (<= bxz-area xyz-area)
         (<= cyx-area xyz-area)))))))

(value-triple :itpeval-statement-checked)
:q
