;; Statement-only formalization of PutnamBench corpus artifact putnam_1965_b6:
;; four distinct points in the real Euclidean plane whose two pencils of
;; circles intersect pairwise are collinear or cocyclic. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative operation symbols below present an arbitrary real-closed
;; ordered field. The field, order, positive-square-root, and odd-degree-root
;; laws are explicit in the statement predicate. Real-closed ordered fields
;; have the same first-order ordered-field theory as the real numbers, so this
;; unbounded coordinate statement is equivalent to its real-plane instance;
;; no coordinate is restricted to a rational or finite surrogate.
;;
;; A point is a pair of field elements. A circle is represented by its center
;; and the squared distance to a point on it. Because all four source points
;; are pairwise distinct, centers equidistant from A,B (respectively C,D) are
;; in bijection with circles through that pair: the positive-square-root law
;; recovers the ordinary radius, and squaring an ordinary distance recovers
;; the equations below. Thus the universally quantified centers and internal
;; intersection witness preserve the source circle hypothesis in both
;; directions. The conclusion retains the source disjunction: the first
;; branch is the two-dimensional collinearity test based at distinct A,B, and
;; the second has an internal center witness equidistant from all four points.

(defstub putnam-1965-b6-real-p (x) t)
(defstub putnam-1965-b6-add-op (x y) t)
(defstub putnam-1965-b6-multiply-op (x y) t)
(defstub putnam-1965-b6-negate-op (x) t)
(defstub putnam-1965-b6-inverse-op (x) t)
(defstub putnam-1965-b6-less-op (x y) t)

(defun putnam-1965-b6-member-p (x)
  (if (putnam-1965-b6-real-p x) t nil))

(defun putnam-1965-b6-add (x y)
  (putnam-1965-b6-add-op x y))

(defun putnam-1965-b6-mul (x y)
  (putnam-1965-b6-multiply-op x y))

(defun putnam-1965-b6-neg (x)
  (putnam-1965-b6-negate-op x))

(defun putnam-1965-b6-inv (x)
  (putnam-1965-b6-inverse-op x))

(defun putnam-1965-b6-less (x y)
  (if (putnam-1965-b6-less-op x y) t nil))

(defun putnam-1965-b6-sub (x y)
  (putnam-1965-b6-add
   x
   (putnam-1965-b6-neg y)))

(defun putnam-1965-b6-square (x)
  (putnam-1965-b6-mul x x))

(defun putnam-1965-b6-positive-p (x zero)
  (and
   (putnam-1965-b6-member-p x)
   (putnam-1965-b6-less zero x)))

(defun-sk putnam-1965-b6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1965-b6-member-p x)
      (putnam-1965-b6-member-p y)
      (putnam-1965-b6-member-p z))
     (and
      (putnam-1965-b6-member-p
       (putnam-1965-b6-add x y))
      (putnam-1965-b6-member-p
       (putnam-1965-b6-mul x y))
      (putnam-1965-b6-member-p
       (putnam-1965-b6-neg x))
      (putnam-1965-b6-member-p
       (putnam-1965-b6-inv x))
      (equal
       (putnam-1965-b6-add
        (putnam-1965-b6-add x y)
        z)
       (putnam-1965-b6-add
        x
        (putnam-1965-b6-add y z)))
      (equal
       (putnam-1965-b6-add x y)
       (putnam-1965-b6-add y x))
      (equal
       (putnam-1965-b6-add x zero)
       x)
      (equal
       (putnam-1965-b6-add
        x
        (putnam-1965-b6-neg x))
       zero)
      (equal
       (putnam-1965-b6-mul
        (putnam-1965-b6-mul x y)
        z)
       (putnam-1965-b6-mul
        x
        (putnam-1965-b6-mul y z)))
      (equal
       (putnam-1965-b6-mul x y)
       (putnam-1965-b6-mul y x))
      (equal
       (putnam-1965-b6-mul x one)
       x)
      (implies
       (equal x zero)
       (equal
        (putnam-1965-b6-inv x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (putnam-1965-b6-mul
         x
         (putnam-1965-b6-inv x))
        one))
      (equal
       (putnam-1965-b6-mul
        x
        (putnam-1965-b6-add y z))
       (putnam-1965-b6-add
        (putnam-1965-b6-mul x y)
        (putnam-1965-b6-mul x z)))))))

(defun-sk putnam-1965-b6-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (putnam-1965-b6-member-p x)
      (putnam-1965-b6-member-p y)
      (putnam-1965-b6-member-p z))
     (and
      (not (putnam-1965-b6-less x x))
      (or
       (equal x y)
       (putnam-1965-b6-less x y)
       (putnam-1965-b6-less y x))
      (implies
       (and
        (putnam-1965-b6-less x y)
        (putnam-1965-b6-less y z))
       (putnam-1965-b6-less x z))
      (implies
       (putnam-1965-b6-less x y)
       (putnam-1965-b6-less
        (putnam-1965-b6-add x z)
        (putnam-1965-b6-add y z)))
      (implies
       (and
        (putnam-1965-b6-less zero x)
        (putnam-1965-b6-less zero y))
       (putnam-1965-b6-less
        zero
        (putnam-1965-b6-mul x y)))))))

(defun putnam-1965-b6-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (putnam-1965-b6-member-p (car coefficients))
     (putnam-1965-b6-polynomial-p (cdr coefficients)))))

(defun putnam-1965-b6-polynomial-value
    (coefficients x zero)
  (if (endp coefficients)
      zero
    (putnam-1965-b6-add
     (car coefficients)
     (putnam-1965-b6-mul
      x
      (putnam-1965-b6-polynomial-value
       (cdr coefficients)
       x
       zero)))))

(defun putnam-1965-b6-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (putnam-1965-b6-leading-coefficient
     (cdr coefficients))))

(defun putnam-1965-b6-odd-degree-p (coefficients zero)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (putnam-1965-b6-leading-coefficient coefficients)
     zero))
   (equal
    (mod (1- (len coefficients)) 2)
    1)))

(defun-sk putnam-1965-b6-square-root-exists-p
    (x zero)
  (exists (root)
    (and
     (or
      (equal root zero)
      (putnam-1965-b6-positive-p root zero))
     (equal
      (putnam-1965-b6-square root)
      x))))

(defun-sk putnam-1965-b6-positive-square-roots-p
    (zero)
  (forall (x)
    (implies
     (putnam-1965-b6-positive-p x zero)
     (putnam-1965-b6-square-root-exists-p
      x
      zero))))

(defun-sk putnam-1965-b6-polynomial-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (putnam-1965-b6-member-p root)
     (equal
      (putnam-1965-b6-polynomial-value
       coefficients
       root
       zero)
      zero))))

(defun-sk putnam-1965-b6-odd-polynomial-roots-p
    (zero)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (putnam-1965-b6-polynomial-p coefficients)
      (putnam-1965-b6-odd-degree-p coefficients zero))
     (putnam-1965-b6-polynomial-root-exists-p
      coefficients
      zero))))

(defun putnam-1965-b6-real-closed-field-p (zero one)
  (and
   (putnam-1965-b6-member-p zero)
   (putnam-1965-b6-member-p one)
   (not (equal zero one))
   (putnam-1965-b6-less zero one)
   (putnam-1965-b6-field-laws-p zero one)
   (putnam-1965-b6-order-laws-p zero)
   (putnam-1965-b6-positive-square-roots-p zero)
   (putnam-1965-b6-odd-polynomial-roots-p zero)))

(defun putnam-1965-b6-point-p (point)
  (and
   (consp point)
   (putnam-1965-b6-member-p (car point))
   (putnam-1965-b6-member-p (cdr point))))

(defun putnam-1965-b6-squared-distance
    (first second)
  (let ((dx
         (putnam-1965-b6-sub
          (car first)
          (car second)))
        (dy
         (putnam-1965-b6-sub
          (cdr first)
          (cdr second))))
    (putnam-1965-b6-add
     (putnam-1965-b6-square dx)
     (putnam-1965-b6-square dy))))

(defun putnam-1965-b6-equidistant-p
    (center first second)
  (equal
   (putnam-1965-b6-squared-distance center first)
   (putnam-1965-b6-squared-distance center second)))

(defun putnam-1965-b6-orientation
    (first second third)
  (putnam-1965-b6-sub
   (putnam-1965-b6-mul
    (putnam-1965-b6-sub
     (car second)
     (car first))
    (putnam-1965-b6-sub
     (cdr third)
     (cdr first)))
   (putnam-1965-b6-mul
    (putnam-1965-b6-sub
     (cdr second)
     (cdr first))
    (putnam-1965-b6-sub
     (car third)
     (car first)))))

(defun putnam-1965-b6-four-distinct-p (a b c d)
  (and
   (not (equal a b))
   (not (equal a c))
   (not (equal a d))
   (not (equal b c))
   (not (equal b d))
   (not (equal c d))))

(defun-sk putnam-1965-b6-intersection-exists-p
    (first-center second-center a c)
  (exists (intersection)
    (and
     (putnam-1965-b6-point-p intersection)
     (equal
      (putnam-1965-b6-squared-distance
       first-center intersection)
      (putnam-1965-b6-squared-distance
       first-center a))
     (equal
      (putnam-1965-b6-squared-distance
       second-center intersection)
      (putnam-1965-b6-squared-distance
       second-center c)))))

(defun-sk putnam-1965-b6-all-circles-intersect-p
    (a b c d)
  (forall (first-center second-center)
    (implies
     (and
      (putnam-1965-b6-point-p first-center)
      (putnam-1965-b6-point-p second-center)
      (putnam-1965-b6-equidistant-p
       first-center a b)
      (putnam-1965-b6-equidistant-p
       second-center c d))
     (putnam-1965-b6-intersection-exists-p
      first-center second-center a c))))

(defun putnam-1965-b6-collinear-p (a b c d zero)
  (and
   (equal
    (putnam-1965-b6-orientation a b c)
    zero)
   (equal
    (putnam-1965-b6-orientation a b d)
    zero)))

(defun-sk putnam-1965-b6-cocyclic-p (a b c d)
  (exists (center)
    (and
     (putnam-1965-b6-point-p center)
     (putnam-1965-b6-equidistant-p center a b)
     (putnam-1965-b6-equidistant-p center a c)
     (putnam-1965-b6-equidistant-p center a d))))

(defun-sk putnambench-putnam-1965-b6-statement
    (zero one)
  (forall (a b c d)
    (implies
     (and
      (putnam-1965-b6-real-closed-field-p zero one)
      (putnam-1965-b6-point-p a)
      (putnam-1965-b6-point-p b)
      (putnam-1965-b6-point-p c)
      (putnam-1965-b6-point-p d)
      (putnam-1965-b6-four-distinct-p a b c d)
      (putnam-1965-b6-all-circles-intersect-p
       a b c d))
     (or
      (putnam-1965-b6-collinear-p
       a b c d zero)
      (putnam-1965-b6-cocyclic-p
       a b c d)))))

(value-triple :itpeval-statement-checked)
:q
