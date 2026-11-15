;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_b6:
;; a tangential real-plane quadrilateral whose area is the square root of the
;; product of its side lengths is cyclic. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar stubs below present an arbitrary real closed ordered field.  All
;; field, order, square-root, and odd-degree-root laws are explicit hypotheses
;; of the statement predicate.  This preserves arbitrary real coordinates:
;; the reals are one such field, and real closed fields have the same
;; first-order theory.
;;
;; The four point arguments are definitionally the values of L on ZMod 4, and
;; pairwise distinctness makes their image exactly S.  Under the source
;; no-three-collinear hypothesis, the boundary-segment condition is equivalent
;; to the four points occurring in one of the two cyclic orientations.
;; Convex-hull membership is then the corresponding four half-plane tests.
;;
;; Euclidean distances are represented by their squared coordinate formulas.
;; Every length variable below is internally existential and constrained to be
;; the unique nonnegative square root.  The shoelace formula gives twice the
;; convex-hull area in cyclic order.  The incircle and circumcircle centers,
;; radii, and tangent points all remain internally quantified.

(defstub p70b6-scalar-p (x) t)
(defstub p70b6-add (x y) t)
(defstub p70b6-mul (x y) t)
(defstub p70b6-neg (x) t)
(defstub p70b6-inv (x) t)
(defstub p70b6-less (x y) t)
(defstub p70b6-square-root (x) t)
(defstub p70b6-odd-root (coefficients) t)

(defun p70b6-member-p (x)
  (if (p70b6-scalar-p x) t nil))

(defun p70b6-less-p (x y)
  (if (p70b6-less x y) t nil))

(defun p70b6-nonnegative-p (zero x)
  (and
   (p70b6-member-p x)
   (not (p70b6-less-p x zero))))

(defun p70b6-sub (x y)
  (p70b6-add x (p70b6-neg y)))

(defun p70b6-square (x)
  (p70b6-mul x x))

(defun p70b6-polynomial-coefficients-p (coefficients)
  (if (consp coefficients)
      (and
       (p70b6-member-p (car coefficients))
       (p70b6-polynomial-coefficients-p (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients are in ascending degree order.
(defun p70b6-polynomial-p (zero coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (p70b6-polynomial-coefficients-p coefficients)
   (or
    (equal (len coefficients) 1)
    (not (equal (car (last coefficients)) zero)))))

(defun p70b6-polynomial-eval (zero coefficients x)
  (if (consp coefficients)
      (p70b6-add
       (car coefficients)
       (p70b6-mul
        x
        (p70b6-polynomial-eval
         zero (cdr coefficients) x)))
    zero))

(defun-sk p70b6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p70b6-member-p x)
      (p70b6-member-p y)
      (p70b6-member-p z))
     (and
      (p70b6-member-p (p70b6-add x y))
      (p70b6-member-p (p70b6-mul x y))
      (p70b6-member-p (p70b6-neg x))
      (p70b6-member-p (p70b6-inv x))
      (equal
       (p70b6-add (p70b6-add x y) z)
       (p70b6-add x (p70b6-add y z)))
      (equal
       (p70b6-mul (p70b6-mul x y) z)
       (p70b6-mul x (p70b6-mul y z)))
      (equal (p70b6-add x y) (p70b6-add y x))
      (equal (p70b6-mul x y) (p70b6-mul y x))
      (equal (p70b6-add x zero) x)
      (equal (p70b6-add x (p70b6-neg x)) zero)
      (equal (p70b6-mul x one) x)
      (implies
       (equal x zero)
       (equal (p70b6-inv x) zero))
      (implies
       (not (equal x zero))
       (equal (p70b6-mul x (p70b6-inv x)) one))
      (equal
       (p70b6-mul x (p70b6-add y z))
       (p70b6-add
        (p70b6-mul x y)
        (p70b6-mul x z)))))))

(defun-sk p70b6-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p70b6-member-p x)
      (p70b6-member-p y)
      (p70b6-member-p z))
     (and
      (not (p70b6-less-p x x))
      (or
       (p70b6-less-p x y)
       (equal x y)
       (p70b6-less-p y x))
      (implies
       (and
        (p70b6-less-p x y)
        (p70b6-less-p y z))
       (p70b6-less-p x z))
      (implies
       (p70b6-less-p x y)
       (p70b6-less-p
        (p70b6-add x z)
        (p70b6-add y z)))
      (implies
       (and
        (p70b6-less-p zero x)
        (p70b6-less-p zero y))
       (p70b6-less-p
        zero
        (p70b6-mul x y)))))))

(defun-sk p70b6-square-root-laws-p (zero)
  (forall (x)
    (implies
     (p70b6-nonnegative-p zero x)
     (and
      (p70b6-nonnegative-p
       zero (p70b6-square-root x))
      (equal
       (p70b6-square (p70b6-square-root x))
       x)))))

(defun-sk p70b6-odd-root-laws-p (zero)
  (forall (coefficients)
    (implies
     (and
      (p70b6-polynomial-p zero coefficients)
      (evenp (len coefficients)))
     (and
      (p70b6-member-p
       (p70b6-odd-root coefficients))
      (equal
       (p70b6-polynomial-eval
        zero
        coefficients
        (p70b6-odd-root coefficients))
       zero)))))

(defun p70b6-real-closed-field-p (zero one)
  (and
   (p70b6-member-p zero)
   (p70b6-member-p one)
   (not (equal zero one))
   (p70b6-less-p zero one)
   (p70b6-field-laws-p zero one)
   (p70b6-order-laws-p zero)
   (p70b6-square-root-laws-p zero)
   (p70b6-odd-root-laws-p zero)))

(defun p70b6-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (p70b6-member-p (nth 0 point))
   (p70b6-member-p (nth 1 point))))

(defun p70b6-distance-squared (left right)
  (p70b6-add
   (p70b6-square
    (p70b6-sub (nth 0 left) (nth 0 right)))
   (p70b6-square
    (p70b6-sub (nth 1 left) (nth 1 right)))))

(defun p70b6-orientation (a b c)
  (p70b6-sub
   (p70b6-mul
    (p70b6-sub (nth 0 b) (nth 0 a))
    (p70b6-sub (nth 1 c) (nth 1 a)))
   (p70b6-mul
    (p70b6-sub (nth 1 b) (nth 1 a))
    (p70b6-sub (nth 0 c) (nth 0 a)))))

(defun p70b6-four-distinct-p (l0 l1 l2 l3)
  (and
   (not (equal l0 l1))
   (not (equal l0 l2))
   (not (equal l0 l3))
   (not (equal l1 l2))
   (not (equal l1 l3))
   (not (equal l2 l3))))

(defun p70b6-general-position-p (zero l0 l1 l2 l3)
  (and
   (not (equal (p70b6-orientation l0 l1 l2) zero))
   (not (equal (p70b6-orientation l0 l1 l3) zero))
   (not (equal (p70b6-orientation l0 l2 l3) zero))
   (not (equal (p70b6-orientation l1 l2 l3) zero))))

(defun p70b6-positive-cyclic-order-p (zero l0 l1 l2 l3)
  (and
   (p70b6-less-p
    zero (p70b6-orientation l0 l1 l2))
   (p70b6-less-p
    zero (p70b6-orientation l1 l2 l3))
   (p70b6-less-p
    zero (p70b6-orientation l2 l3 l0))
   (p70b6-less-p
    zero (p70b6-orientation l3 l0 l1))))

(defun p70b6-negative-cyclic-order-p (zero l0 l1 l2 l3)
  (and
   (p70b6-less-p
    (p70b6-orientation l0 l1 l2) zero)
   (p70b6-less-p
    (p70b6-orientation l1 l2 l3) zero)
   (p70b6-less-p
    (p70b6-orientation l2 l3 l0) zero)
   (p70b6-less-p
    (p70b6-orientation l3 l0 l1) zero)))

(defun p70b6-boundary-order-p (zero l0 l1 l2 l3)
  (or
   (p70b6-positive-cyclic-order-p
    zero l0 l1 l2 l3)
   (p70b6-negative-cyclic-order-p
    zero l0 l1 l2 l3)))

(defun p70b6-positive-side-lengths-p
    (zero l0 l1 l2 l3)
  (and
   (p70b6-less-p
    zero (p70b6-distance-squared l0 l1))
   (p70b6-less-p
    zero (p70b6-distance-squared l1 l2))
   (p70b6-less-p
    zero (p70b6-distance-squared l2 l3))
   (p70b6-less-p
    zero (p70b6-distance-squared l3 l0))))

(defun p70b6-center-in-hull-p
    (zero center l0 l1 l2 l3)
  (if (p70b6-positive-cyclic-order-p
       zero l0 l1 l2 l3)
      (and
       (p70b6-nonnegative-p
        zero (p70b6-orientation l0 l1 center))
       (p70b6-nonnegative-p
        zero (p70b6-orientation l1 l2 center))
       (p70b6-nonnegative-p
        zero (p70b6-orientation l2 l3 center))
       (p70b6-nonnegative-p
        zero (p70b6-orientation l3 l0 center)))
    (and
     (p70b6-nonnegative-p
      zero (p70b6-neg
            (p70b6-orientation l0 l1 center)))
     (p70b6-nonnegative-p
      zero (p70b6-neg
            (p70b6-orientation l1 l2 center)))
     (p70b6-nonnegative-p
      zero (p70b6-neg
            (p70b6-orientation l2 l3 center)))
     (p70b6-nonnegative-p
      zero (p70b6-neg
            (p70b6-orientation l3 l0 center))))))

(defun p70b6-tangent-point-p
    (zero center radius a b point)
  (and
   (p70b6-point-p point)
   (equal (p70b6-orientation a b point) zero)
   (equal
    (p70b6-distance-squared center point)
    (p70b6-square radius))))

(defun-sk p70b6-tangent-point-exists-p
    (zero center radius a b)
  (exists (point)
    (p70b6-tangent-point-p
     zero center radius a b point)))

(defun-sk p70b6-tangent-point-unique-p
    (zero center radius a b)
  (forall (left right)
    (implies
     (and
      (p70b6-tangent-point-p
       zero center radius a b left)
      (p70b6-tangent-point-p
       zero center radius a b right))
     (equal left right))))

(defun p70b6-side-tangent-p
    (zero center radius a b)
  (and
   (p70b6-tangent-point-exists-p
    zero center radius a b)
   (p70b6-tangent-point-unique-p
    zero center radius a b)))

(defun-sk p70b6-incircle-exists-p
    (zero l0 l1 l2 l3)
  (exists (center radius)
    (and
     (p70b6-point-p center)
     (p70b6-member-p radius)
     (p70b6-less-p zero radius)
     (p70b6-center-in-hull-p
      zero center l0 l1 l2 l3)
     (p70b6-side-tangent-p
      zero center radius l0 l1)
     (p70b6-side-tangent-p
      zero center radius l1 l2)
     (p70b6-side-tangent-p
      zero center radius l2 l3)
     (p70b6-side-tangent-p
      zero center radius l3 l0))))

(defun p70b6-origin-cross (a b)
  (p70b6-sub
   (p70b6-mul (nth 0 a) (nth 1 b))
   (p70b6-mul (nth 1 a) (nth 0 b))))

(defun p70b6-twice-signed-area (l0 l1 l2 l3)
  (p70b6-add
   (p70b6-origin-cross l0 l1)
   (p70b6-add
    (p70b6-origin-cross l1 l2)
    (p70b6-add
     (p70b6-origin-cross l2 l3)
     (p70b6-origin-cross l3 l0)))))

(defun p70b6-absolute-value (zero x)
  (if (p70b6-less-p x zero)
      (p70b6-neg x)
    x))

(defun p70b6-length-value-p (zero a b length)
  (and
   (p70b6-nonnegative-p zero length)
   (equal
    (p70b6-square length)
    (p70b6-distance-squared a b))))

(defun p70b6-area-value-p
    (zero one l0 l1 l2 l3 area)
  (and
   (p70b6-nonnegative-p zero area)
   (equal
    (p70b6-mul
     (p70b6-add one one)
     area)
    (p70b6-absolute-value
     zero
     (p70b6-twice-signed-area
      l0 l1 l2 l3)))))

(defun p70b6-square-root-value-p (zero value root)
  (and
   (p70b6-nonnegative-p zero root)
   (equal (p70b6-square root) value)))

(defun-sk p70b6-area-identity-p
    (zero one l0 l1 l2 l3)
  (exists (a b c d area root)
    (and
     (p70b6-length-value-p zero l0 l1 a)
     (p70b6-length-value-p zero l1 l2 b)
     (p70b6-length-value-p zero l2 l3 c)
     (p70b6-length-value-p zero l3 l0 d)
     (p70b6-area-value-p
      zero one l0 l1 l2 l3 area)
     (p70b6-square-root-value-p
      zero
      (p70b6-mul
       a
       (p70b6-mul
        b
        (p70b6-mul c d)))
      root)
     (equal area root))))

(defun-sk p70b6-cospherical-p
    (zero l0 l1 l2 l3)
  (exists (center radius)
    (and
     (p70b6-point-p center)
     (p70b6-nonnegative-p zero radius)
     (equal
      (p70b6-distance-squared l0 center)
      (p70b6-square radius))
     (equal
      (p70b6-distance-squared l1 center)
      (p70b6-square radius))
     (equal
      (p70b6-distance-squared l2 center)
      (p70b6-square radius))
     (equal
      (p70b6-distance-squared l3 center)
      (p70b6-square radius)))))

(defun putnambench-putnam-1970-b6-statement
    (zero one l0 l1 l2 l3)
  (implies
   (and
    (p70b6-real-closed-field-p zero one)
    (p70b6-point-p l0)
    (p70b6-point-p l1)
    (p70b6-point-p l2)
    (p70b6-point-p l3)
    (p70b6-four-distinct-p l0 l1 l2 l3)
    (p70b6-general-position-p
     zero l0 l1 l2 l3)
    (p70b6-positive-side-lengths-p
     zero l0 l1 l2 l3)
    (p70b6-boundary-order-p
     zero l0 l1 l2 l3)
    (p70b6-incircle-exists-p
     zero l0 l1 l2 l3)
    (p70b6-area-identity-p
     zero one l0 l1 l2 l3))
   (p70b6-cospherical-p
    zero l0 l1 l2 l3)))

(value-triple :itpeval-statement-checked)
:q
