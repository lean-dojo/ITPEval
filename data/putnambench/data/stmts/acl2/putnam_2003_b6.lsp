;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_b6:
;; every continuous real-valued function on the unit interval satisfies the
;; stated lower bound comparing a double integral of |f(x)+f(y)| with the
;; integral of |f(x)|. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A code is a rational polygonal function on [0,1], with strictly increasing
;; rational knots beginning at 0 and ending at 1. Extending it constantly
;; outside [0,1] gives a globally continuous real function, as required by the
;; ground-truth statements.
;;
;; This is an exact counterexample-preserving encoding, not a restriction to
;; a fixed grid or a finite table. Rational polygonal functions with arbitrary
;; finite knot lists are uniformly dense in the continuous real functions on
;; [0,1]. If ||f-g||_infinity <= delta, then
;;
;;   | integral integral |f(x)+f(y)| - integral integral |g(x)+g(y)| |
;;     <= 2*delta
;;
;; and
;;
;;   | integral |f(x)| - integral |g(x)| | <= delta.
;;
;; Hence any strict failure of the source inequality survives a sufficiently
;; close rational polygonal approximation. Conversely, every code denotes a
;; source function. Thus universal validity for these codes is bidirectionally
;; equivalent to universal validity for the source continuous functions.
;;
;; All integrals below are exact rational integrals of the denoted polygonal
;; functions. On a pair of knot intervals, f(x)+f(y) is affine in (x,y).
;; The mixed second derivative of |z|^3 is 6*|z|, which gives the exact
;; four-corner formula used for a rectangle when both slopes are nonzero.

(defun putnam-2003-b6-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (rationalp (car point))
   (rationalp (cadr point))))

(defun putnam-2003-b6-point-x (point)
  (car point))

(defun putnam-2003-b6-point-y (point)
  (cadr point))

(defun putnam-2003-b6-last-point (points)
  (if (consp (cdr points))
      (putnam-2003-b6-last-point (cdr points))
    (car points)))

(defun putnam-2003-b6-points-p (points)
  (if (consp points)
      (and
       (putnam-2003-b6-point-p (car points))
       (putnam-2003-b6-points-p (cdr points)))
    (equal points nil)))

(defun putnam-2003-b6-strict-knots-p (points)
  (if (consp (cdr points))
      (and
       (< (putnam-2003-b6-point-x (car points))
          (putnam-2003-b6-point-x (cadr points)))
       (putnam-2003-b6-strict-knots-p (cdr points)))
    t))

(defun putnam-2003-b6-polygon-p (points)
  (and
   (true-listp points)
   (consp points)
   (consp (cdr points))
   (putnam-2003-b6-points-p points)
   (equal (putnam-2003-b6-point-x (car points)) 0)
   (equal
    (putnam-2003-b6-point-x
     (putnam-2003-b6-last-point points))
    1)
   (putnam-2003-b6-strict-knots-p points)))

(defun putnam-2003-b6-segment-width (left right)
  (- (putnam-2003-b6-point-x right)
     (putnam-2003-b6-point-x left)))

(defun putnam-2003-b6-segment-slope (left right)
  (/ (- (putnam-2003-b6-point-y right)
        (putnam-2003-b6-point-y left))
     (putnam-2003-b6-segment-width left right)))

;; Exact integral of the absolute value of an affine function on an interval,
;; specified by its endpoint values and the interval width.
(defun putnam-2003-b6-abs-affine-integral
    (left-value right-value width)
  (if (< (* left-value right-value) 0)
      (/ (* width
            (+ (* left-value left-value)
               (* right-value right-value)))
         (* 2
            (+ (abs left-value)
               (abs right-value))))
    (/ (* width
          (+ (abs left-value)
             (abs right-value)))
       2)))

(defun putnam-2003-b6-segment-abs-integral (left right)
  (putnam-2003-b6-abs-affine-integral
   (putnam-2003-b6-point-y left)
   (putnam-2003-b6-point-y right)
   (putnam-2003-b6-segment-width left right)))

(defun putnam-2003-b6-abs-integral (points)
  (if (consp (cdr points))
      (+ (putnam-2003-b6-segment-abs-integral
          (car points) (cadr points))
         (putnam-2003-b6-abs-integral (cdr points)))
    0))

(defun putnam-2003-b6-abs-cube (value)
  (* (abs value) (abs value) (abs value)))

;; Exact integral of |f(x)+f(y)| over one rectangle formed by two polygon
;; segments. V00, V10, V01, and V11 are the affine function's corner values.
(defun putnam-2003-b6-segment-pair-integral
    (x-left x-right y-left y-right)
  (let* ((x-width
          (putnam-2003-b6-segment-width x-left x-right))
         (y-width
          (putnam-2003-b6-segment-width y-left y-right))
         (x-slope
          (putnam-2003-b6-segment-slope x-left x-right))
         (y-slope
          (putnam-2003-b6-segment-slope y-left y-right))
         (v00
          (+ (putnam-2003-b6-point-y x-left)
             (putnam-2003-b6-point-y y-left)))
         (v10
          (+ (putnam-2003-b6-point-y x-right)
             (putnam-2003-b6-point-y y-left)))
         (v01
          (+ (putnam-2003-b6-point-y x-left)
             (putnam-2003-b6-point-y y-right)))
         (v11
          (+ (putnam-2003-b6-point-y x-right)
             (putnam-2003-b6-point-y y-right))))
    (cond
     ((equal x-slope 0)
      (if (equal y-slope 0)
          (* x-width y-width (abs v00))
        (* x-width
           (putnam-2003-b6-abs-affine-integral
            v00 v01 y-width))))
     ((equal y-slope 0)
      (* y-width
         (putnam-2003-b6-abs-affine-integral
          v00 v10 x-width)))
     (t
      (/ (+ (putnam-2003-b6-abs-cube v11)
            (- (putnam-2003-b6-abs-cube v10))
            (- (putnam-2003-b6-abs-cube v01))
            (putnam-2003-b6-abs-cube v00))
         (* 6 x-slope y-slope))))))

(defun putnam-2003-b6-y-segments-integral
    (x-left x-right y-points)
  (if (consp (cdr y-points))
      (+ (putnam-2003-b6-segment-pair-integral
          x-left x-right (car y-points) (cadr y-points))
         (putnam-2003-b6-y-segments-integral
          x-left x-right (cdr y-points)))
    0))

(defun putnam-2003-b6-double-abs-integral-aux
    (x-points all-points)
  (if (consp (cdr x-points))
      (+ (putnam-2003-b6-y-segments-integral
          (car x-points) (cadr x-points) all-points)
         (putnam-2003-b6-double-abs-integral-aux
          (cdr x-points) all-points))
    0))

(defun putnam-2003-b6-double-abs-integral (points)
  (putnam-2003-b6-double-abs-integral-aux points points))

(defun putnambench-putnam-2003-b6-statement (points)
  (implies
   (putnam-2003-b6-polygon-p points)
   (<= (putnam-2003-b6-abs-integral points)
       (putnam-2003-b6-double-abs-integral points))))

(value-triple :itpeval-statement-checked)
:q
