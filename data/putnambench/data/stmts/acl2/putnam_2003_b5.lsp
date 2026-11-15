;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_b5:
;; for three equidistant noncoincident points on the unit circle, the
;; distances from an interior point are the side lengths of a triangle whose
;; area depends only on the point's distance from the origin. This file
;; contains no proof and does not prescribe the area function or a triangle.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar symbols present an arbitrary real-closed ordered field. The
;; theorem is semialgebraic after eliminating the auxiliary area function as
;; explained below, so completeness of real-closed fields makes this
;; presentation equivalent to the statement over the real numbers.

(defstub p2003b5-scalar-p (x) t)
(defstub p2003b5-add-op (x y) t)
(defstub p2003b5-multiply-op (x y) t)
(defstub p2003b5-negate-op (x) t)
(defstub p2003b5-inverse-op (x) t)
(defstub p2003b5-less-op (x y) t)
(defstub p2003b5-zero () t)
(defstub p2003b5-one () t)

(defun p2003b5-add (x y)
  (p2003b5-add-op x y))

(defun p2003b5-multiply (x y)
  (p2003b5-multiply-op x y))

(defun p2003b5-negate (x)
  (p2003b5-negate-op x))

(defun p2003b5-inverse (x)
  (p2003b5-inverse-op x))

(defun p2003b5-subtract (x y)
  (p2003b5-add x (p2003b5-negate y)))

(defun p2003b5-less (x y)
  (if (p2003b5-less-op x y) t nil))

(defun p2003b5-nonnegative-p (x)
  (and
   (p2003b5-scalar-p x)
   (not (p2003b5-less x (p2003b5-zero)))))

(defun p2003b5-positive-p (x)
  (and
   (p2003b5-scalar-p x)
   (p2003b5-less (p2003b5-zero) x)))

(defun-sk p2003b5-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p2003b5-scalar-p x)
      (p2003b5-scalar-p y)
      (p2003b5-scalar-p z))
     (and
      (p2003b5-scalar-p (p2003b5-add x y))
      (p2003b5-scalar-p (p2003b5-multiply x y))
      (p2003b5-scalar-p (p2003b5-negate x))
      (implies
       (not (equal x (p2003b5-zero)))
       (p2003b5-scalar-p (p2003b5-inverse x)))
      (equal
       (p2003b5-add (p2003b5-add x y) z)
       (p2003b5-add x (p2003b5-add y z)))
      (equal
       (p2003b5-add x y)
       (p2003b5-add y x))
      (equal
       (p2003b5-add x (p2003b5-zero))
       x)
      (equal
       (p2003b5-add x (p2003b5-negate x))
       (p2003b5-zero))
      (equal
       (p2003b5-multiply
        (p2003b5-multiply x y) z)
       (p2003b5-multiply
        x (p2003b5-multiply y z)))
      (equal
       (p2003b5-multiply x y)
       (p2003b5-multiply y x))
      (equal
       (p2003b5-multiply x (p2003b5-one))
       x)
      (implies
       (not (equal x (p2003b5-zero)))
       (equal
        (p2003b5-multiply x (p2003b5-inverse x))
        (p2003b5-one)))
      (equal
       (p2003b5-multiply x (p2003b5-add y z))
       (p2003b5-add
        (p2003b5-multiply x y)
        (p2003b5-multiply x z)))))))

(defun-sk p2003b5-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p2003b5-scalar-p x)
      (p2003b5-scalar-p y)
      (p2003b5-scalar-p z))
     (and
      (not (p2003b5-less x x))
      (or
       (equal x y)
       (p2003b5-less x y)
       (p2003b5-less y x))
      (implies
       (and
        (p2003b5-less x y)
        (p2003b5-less y z))
       (p2003b5-less x z))
      (implies
       (p2003b5-less x y)
       (p2003b5-less
        (p2003b5-add x z)
        (p2003b5-add y z)))
      (implies
       (and
        (p2003b5-less (p2003b5-zero) x)
        (p2003b5-less (p2003b5-zero) y))
       (p2003b5-less
        (p2003b5-zero)
        (p2003b5-multiply x y)))))))

(defun p2003b5-carrier-list-p (coefficients)
  (if (consp coefficients)
      (and
       (p2003b5-scalar-p (car coefficients))
       (p2003b5-carrier-list-p (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients are stored in increasing degree order.
(defun p2003b5-polynomial-value (coefficients x)
  (if (consp coefficients)
      (p2003b5-add
       (car coefficients)
       (p2003b5-multiply
        x
        (p2003b5-polynomial-value
         (cdr coefficients) x)))
    (p2003b5-zero)))

(defun p2003b5-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (p2003b5-carrier-list-p coefficients)))

(defun p2003b5-odd-degree-polynomial-p (coefficients)
  (and
   (p2003b5-polynomial-p coefficients)
   (consp coefficients)
   ;; Degree LEN-1 is odd exactly when LEN is even.
   (evenp (len coefficients))
   (not
    (equal
     (car (last coefficients))
     (p2003b5-zero)))))

(defun-sk p2003b5-square-root-exists-p (x)
  (exists (root)
    (and
     (p2003b5-scalar-p root)
     (equal
      (p2003b5-multiply root root)
      x))))

(defun-sk p2003b5-positive-square-roots-p ()
  (forall (x)
    (implies
     (p2003b5-positive-p x)
     (p2003b5-square-root-exists-p x))))

(defun-sk p2003b5-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (p2003b5-scalar-p root)
     (equal
      (p2003b5-polynomial-value coefficients root)
      (p2003b5-zero)))))

(defun-sk p2003b5-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (p2003b5-odd-degree-polynomial-p coefficients)
     (p2003b5-polynomial-root-exists-p
      coefficients))))

(defun p2003b5-real-closed-field-p ()
  (and
   (p2003b5-scalar-p (p2003b5-zero))
   (p2003b5-scalar-p (p2003b5-one))
   (not (equal (p2003b5-zero) (p2003b5-one)))
   (p2003b5-less (p2003b5-zero) (p2003b5-one))
   (p2003b5-field-laws-p)
   (p2003b5-order-laws-p)
   (p2003b5-positive-square-roots-p)
   (p2003b5-odd-polynomial-roots-p)))

(defun p2003b5-square (x)
  (p2003b5-multiply x x))

(defun p2003b5-two ()
  (p2003b5-add
   (p2003b5-one)
   (p2003b5-one)))

(defun p2003b5-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (p2003b5-scalar-p (nth 0 point))
   (p2003b5-scalar-p (nth 1 point))))

(defun p2003b5-point-subtract (left right)
  (list
   (p2003b5-subtract
    (nth 0 left) (nth 0 right))
   (p2003b5-subtract
    (nth 1 left) (nth 1 right))))

(defun p2003b5-dot (left right)
  (p2003b5-add
   (p2003b5-multiply
    (nth 0 left) (nth 0 right))
   (p2003b5-multiply
    (nth 1 left) (nth 1 right))))

(defun p2003b5-norm-squared (point)
  (p2003b5-dot point point))

(defun p2003b5-distance-squared (left right)
  (p2003b5-norm-squared
   (p2003b5-point-subtract left right)))

(defun p2003b5-cross (left right)
  (p2003b5-subtract
   (p2003b5-multiply
    (nth 0 left) (nth 1 right))
   (p2003b5-multiply
    (nth 1 left) (nth 0 right))))

(defun p2003b5-twice-oriented-area (x y z)
  (p2003b5-cross
   (p2003b5-point-subtract y x)
   (p2003b5-point-subtract z x)))

(defun p2003b5-configuration-p (a b c)
  (and
   (p2003b5-point-p a)
   (p2003b5-point-p b)
   (p2003b5-point-p c)
   (equal
    (p2003b5-norm-squared a)
    (p2003b5-one))
   (equal
    (p2003b5-norm-squared b)
    (p2003b5-one))
   (equal
    (p2003b5-norm-squared c)
    (p2003b5-one))
   (equal
    (p2003b5-distance-squared a b)
    (p2003b5-distance-squared a c))
   (equal
    (p2003b5-distance-squared a b)
    (p2003b5-distance-squared b c))
   (not
    (equal
     (p2003b5-distance-squared a b)
     (p2003b5-zero)))))

(defun p2003b5-triangle-witness-p
    (a b c p area x y z)
  (and
   (p2003b5-point-p x)
   (p2003b5-point-p y)
   (p2003b5-point-p z)
   (p2003b5-scalar-p area)
   (p2003b5-nonnegative-p area)
   (equal
    (p2003b5-distance-squared x y)
    (p2003b5-distance-squared p a))
   (equal
    (p2003b5-distance-squared y z)
    (p2003b5-distance-squared p b))
   (equal
    (p2003b5-distance-squared x z)
    (p2003b5-distance-squared p c))
   ;; Euclidean triangle area is |cross(y-x,z-x)| / 2. Both sides are
   ;; nonnegative, so equality of their squares is exactly area equality.
   (equal
    (p2003b5-square
     (p2003b5-multiply
      (p2003b5-two) area))
    (p2003b5-square
     (p2003b5-twice-oriented-area x y z)))))

(defun-sk p2003b5-triangle-exists-p
    (a b c p area)
  (exists (x y z)
    (p2003b5-triangle-witness-p
     a b c p area x y z)))

(defun-sk p2003b5-area-valid-for-radius-squared-p
    (a b c radius-squared area)
  (forall (p)
    (implies
     (and
      (p2003b5-point-p p)
      (equal
       (p2003b5-norm-squared p)
       radius-squared))
     (p2003b5-triangle-exists-p
      a b c p area))))

(defun p2003b5-area-witness-p
    (a b c radius-squared area)
  (and
   (p2003b5-scalar-p area)
   (p2003b5-nonnegative-p area)
   (p2003b5-area-valid-for-radius-squared-p
    a b c radius-squared area)))

(defun-sk p2003b5-area-exists-for-radius-squared-p
    (a b c radius-squared)
  (exists (area)
    (p2003b5-area-witness-p
     a b c radius-squared area)))

;; Replacing radius r by radius-squared rho is exact on 0 <= r < 1 because
;; r |-> r^2 is a bijection there. Thus
;;
;;   exists f, forall P, exists triangle with area f(||P||)
;;
;; is equivalent (using ordinary choice) to the first-order statement below:
;; for every rho in [0,1), one common area works for every P with ||P||^2=rho.
;; This preserves the source quantifiers without hard-coding the solved area.

(defun-sk p2003b5-all-interior-radii-p (a b c)
  (forall (radius-squared)
    (implies
     (and
      (p2003b5-scalar-p radius-squared)
      (p2003b5-nonnegative-p radius-squared)
      (p2003b5-less
       radius-squared
       (p2003b5-one)))
     (p2003b5-area-exists-for-radius-squared-p
      a b c radius-squared))))

(defun putnambench-putnam-2003-b5-statement (a b c)
  (implies
   (and
    (p2003b5-real-closed-field-p)
    (p2003b5-configuration-p a b c))
   (p2003b5-all-interior-radii-p a b c)))

(value-triple :itpeval-statement-checked)
:q
