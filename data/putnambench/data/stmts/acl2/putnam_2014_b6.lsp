;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_b6:
;; a Lipschitz real function on [0,1] with integer-affine values at rational
;; points has a finite closed-interval cover on which it is affine. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; PUTNAM-2014-B6-F-APPROX is the rational regular-Cauchy presentation of the
;; restriction of the arbitrary source function to rational points of [0,1].
;; DEFSTUB keeps that function generic; every property used below is an
;; explicit hypothesis of the statement predicate.
(defstub putnam-2014-b6-f-approx (x epsilon) t)

(defun putnam-2014-b6-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun putnam-2014-b6-unit-rational-p (x)
  (and (rationalp x)
       (<= 0 x)
       (<= x 1)))

(defun-sk putnam-2014-b6-regular-cauchy-values-p ()
  (forall (x epsilon eta)
    (implies
     (and
      (putnam-2014-b6-unit-rational-p x)
      (putnam-2014-b6-positive-rational-p epsilon)
      (putnam-2014-b6-positive-rational-p eta))
     (and
      (rationalp
       (putnam-2014-b6-f-approx x epsilon))
      (rationalp
       (putnam-2014-b6-f-approx x eta))
      (<=
       (abs
        (-
         (putnam-2014-b6-f-approx x epsilon)
         (putnam-2014-b6-f-approx x eta)))
       (+ epsilon eta))))))

;; Requiring the displayed inequality for every positive rational ERROR is
;; exactly the Lipschitz inequality for the real limits of the Cauchy names.
(defun-sk putnam-2014-b6-lipschitz-bound-p (k)
  (forall (x y error)
    (implies
     (and
      (putnam-2014-b6-unit-rational-p x)
      (putnam-2014-b6-unit-rational-p y)
      (putnam-2014-b6-positive-rational-p error))
     (<=
      (abs
       (-
        (putnam-2014-b6-f-approx x (/ error 4))
        (putnam-2014-b6-f-approx y (/ error 4))))
      (+
       (* k (abs (- x y)))
       error)))))

(defun putnam-2014-b6-positive-lipschitz-bound-p (k)
  (and
   (putnam-2014-b6-positive-rational-p k)
   (putnam-2014-b6-lipschitz-bound-p k)))

(defun-sk putnam-2014-b6-lipschitz-p ()
  (exists (k)
    (putnam-2014-b6-positive-lipschitz-bound-p k)))

(defun-sk putnam-2014-b6-equals-rational-p (x value)
  (forall (epsilon)
    (implies
     (putnam-2014-b6-positive-rational-p epsilon)
     (and
      (rationalp
       (putnam-2014-b6-f-approx x epsilon))
      (<=
       (abs
        (-
         (putnam-2014-b6-f-approx x epsilon)
         value))
       epsilon)))))

(defun putnam-2014-b6-integer-affine-witness-p
    (x a b)
  (and
   (integerp a)
   (integerp b)
   (putnam-2014-b6-equals-rational-p
    x (+ a (* b x)))))

(defun-sk putnam-2014-b6-integer-affine-value-p (x)
  (exists (a b)
    (putnam-2014-b6-integer-affine-witness-p
     x a b)))

(defun-sk putnam-2014-b6-rational-values-p ()
  (forall (x)
    (implies
     (putnam-2014-b6-unit-rational-p x)
     (putnam-2014-b6-integer-affine-value-p x))))

;; A piece is (LEFT RIGHT SLOPE INTERCEPT). Under the rational-value
;; hypothesis, a finite real affine cover exists iff one exists with all four
;; entries rational: nondegenerate pieces have rational affine coefficients,
;; and transitions between distinct such formulas occur at rational points.
(defun putnam-2014-b6-piece-p (piece)
  (and
   (true-listp piece)
   (equal (len piece) 4)
   (rationalp (car piece))
   (rationalp (cadr piece))
   (rationalp (caddr piece))
   (rationalp (cadddr piece))
   (<= 0 (car piece))
   (<= (car piece) (cadr piece))
   (<= (cadr piece) 1)))

(defun putnam-2014-b6-pieces-p (pieces)
  (if (consp pieces)
      (and
       (putnam-2014-b6-piece-p (car pieces))
       (putnam-2014-b6-pieces-p (cdr pieces)))
    (equal pieces nil)))

(defun putnam-2014-b6-piece-contains-p (piece x)
  (and
   (<= (car piece) x)
   (<= x (cadr piece))))

(defun putnam-2014-b6-some-piece-contains-p
    (pieces x)
  (if (consp pieces)
      (or
       (putnam-2014-b6-piece-contains-p
        (car pieces) x)
       (putnam-2014-b6-some-piece-contains-p
        (cdr pieces) x))
    nil))

(defun-sk putnam-2014-b6-covers-unit-interval-p
    (pieces)
  (forall (x)
    (implies
     (putnam-2014-b6-unit-rational-p x)
     (putnam-2014-b6-some-piece-contains-p
      pieces x))))

(defun-sk putnam-2014-b6-piece-linear-p (piece)
  (forall (x)
    (implies
     (and
      (rationalp x)
      (putnam-2014-b6-piece-contains-p piece x))
     (putnam-2014-b6-equals-rational-p
      x
      (+
       (cadddr piece)
       (* (caddr piece) x))))))

(defun putnam-2014-b6-pieces-linear-p (pieces)
  (if (consp pieces)
      (and
       (putnam-2014-b6-piece-linear-p
        (car pieces))
       (putnam-2014-b6-pieces-linear-p
        (cdr pieces)))
    (equal pieces nil)))

(defun putnam-2014-b6-cover-witness-p (pieces)
  (and
   (true-listp pieces)
   (consp pieces)
   (putnam-2014-b6-pieces-p pieces)
   (putnam-2014-b6-covers-unit-interval-p pieces)
   (putnam-2014-b6-pieces-linear-p pieces)))

(defun-sk putnam-2014-b6-affine-cover-exists-p ()
  (exists (pieces)
    (putnam-2014-b6-cover-witness-p pieces)))

(defun putnambench-putnam-2014-b6-statement ()
  (implies
   (and
    (putnam-2014-b6-regular-cauchy-values-p)
    (putnam-2014-b6-lipschitz-p)
    (putnam-2014-b6-rational-values-p))
   (putnam-2014-b6-affine-cover-exists-p)))

(value-triple :itpeval-statement-checked)
:q
