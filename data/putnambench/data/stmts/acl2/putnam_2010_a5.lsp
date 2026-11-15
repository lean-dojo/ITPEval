;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_a5:
;; a group embedded in real three-space whose product is always either the
;; vector cross product or zero has identically zero cross products. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The arbitrary group and its embedding are conservative generic symbols.
;; PUTNAM-2010-A5-COORD-APPROX gives rational regular-Cauchy approximations
;; to each of the three real coordinates of an embedded group element.
;; Any source counterexample would persist in the countable subgroup generated
;; by its failing pair, so representing group elements by ACL2 objects does not
;; restrict the theorem. The internal precision quantifiers below make the
;; Cauchy-name comparisons exact equalities of represented real numbers.
(defstub putnam-2010-a5-group-member-p (x) t)
(defstub putnam-2010-a5-group-mul (x y) t)
(defstub putnam-2010-a5-group-inverse (x) t)
(defstub putnam-2010-a5-group-one () t)
(defstub putnam-2010-a5-coord-approx (x axis epsilon) t)

(defun putnam-2010-a5-axis-p (axis)
  (and (integerp axis)
       (<= 0 axis)
       (< axis 3)))

(defun putnam-2010-a5-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

;; Every coordinate name converges to a unique real number, and every real
;; coordinate admits such a name.
(defun-sk putnam-2010-a5-regular-embedding-p ()
  (forall (x axis epsilon eta)
    (implies
     (and
      (putnam-2010-a5-group-member-p x)
      (putnam-2010-a5-axis-p axis)
      (putnam-2010-a5-positive-rational-p epsilon)
      (putnam-2010-a5-positive-rational-p eta))
     (let ((left
            (putnam-2010-a5-coord-approx
             x axis epsilon))
           (right
            (putnam-2010-a5-coord-approx
             x axis eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; For regular names this is exactly equality of their represented reals.
(defun-sk putnam-2010-a5-coordinate-equal-p
    (x y axis)
  (forall (epsilon)
    (implies
     (putnam-2010-a5-positive-rational-p epsilon)
     (<=
      (abs
       (-
        (putnam-2010-a5-coord-approx
         x axis epsilon)
        (putnam-2010-a5-coord-approx
         y axis epsilon)))
      (* 2 epsilon)))))

(defun putnam-2010-a5-embedded-vector-equal-p (x y)
  (and
   (putnam-2010-a5-coordinate-equal-p x y 0)
   (putnam-2010-a5-coordinate-equal-p x y 1)
   (putnam-2010-a5-coordinate-equal-p x y 2)))

(defun-sk putnam-2010-a5-embedding-injective-p ()
  (forall (x y)
    (implies
     (and
      (putnam-2010-a5-group-member-p x)
      (putnam-2010-a5-group-member-p y)
      (putnam-2010-a5-embedded-vector-equal-p x y))
     (equal x y))))

(defun-sk putnam-2010-a5-group-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-2010-a5-group-member-p x)
      (putnam-2010-a5-group-member-p y)
      (putnam-2010-a5-group-member-p z))
     (and
      (putnam-2010-a5-group-member-p
       (putnam-2010-a5-group-mul x y))
      (putnam-2010-a5-group-member-p
       (putnam-2010-a5-group-inverse x))
      (equal
       (putnam-2010-a5-group-mul
        (putnam-2010-a5-group-mul x y)
        z)
       (putnam-2010-a5-group-mul
        x
        (putnam-2010-a5-group-mul y z)))
      (equal
       (putnam-2010-a5-group-mul
        (putnam-2010-a5-group-one)
        x)
       x)
      (equal
       (putnam-2010-a5-group-mul
        x
        (putnam-2010-a5-group-one))
       x)
      (equal
       (putnam-2010-a5-group-mul
        (putnam-2010-a5-group-inverse x)
        x)
       (putnam-2010-a5-group-one))
      (equal
       (putnam-2010-a5-group-mul
        x
        (putnam-2010-a5-group-inverse x))
       (putnam-2010-a5-group-one))))))

(defun putnam-2010-a5-group-p ()
  (and
   (putnam-2010-a5-group-member-p
    (putnam-2010-a5-group-one))
   (putnam-2010-a5-group-laws-p)))

(defun putnam-2010-a5-cross-coordinate-sample
    (x y axis precision)
  (cond
   ((equal axis 0)
    (-
     (*
      (putnam-2010-a5-coord-approx x 1 precision)
      (putnam-2010-a5-coord-approx y 2 precision))
     (*
      (putnam-2010-a5-coord-approx x 2 precision)
      (putnam-2010-a5-coord-approx y 1 precision))))
   ((equal axis 1)
    (-
     (*
      (putnam-2010-a5-coord-approx x 2 precision)
      (putnam-2010-a5-coord-approx y 0 precision))
     (*
      (putnam-2010-a5-coord-approx x 0 precision)
      (putnam-2010-a5-coord-approx y 2 precision))))
   (t
    (-
     (*
      (putnam-2010-a5-coord-approx x 0 precision)
      (putnam-2010-a5-coord-approx y 1 precision))
     (*
      (putnam-2010-a5-coord-approx x 1 precision)
      (putnam-2010-a5-coord-approx y 0 precision))))))

;; As precision tends to zero, the sample converges to the corresponding
;; coordinate of the usual cross product.
(defun putnam-2010-a5-cross-target-witness-p
    (x y target axis epsilon precision)
  (and
   (putnam-2010-a5-positive-rational-p precision)
   (<= precision epsilon)
   (<=
    (abs
     (-
      (putnam-2010-a5-cross-coordinate-sample
       x y axis precision)
      (putnam-2010-a5-coord-approx
       target axis precision)))
    epsilon)))

(defun-sk putnam-2010-a5-cross-target-precision-p
    (x y target axis epsilon)
  (exists (precision)
    (putnam-2010-a5-cross-target-witness-p
     x y target axis epsilon precision)))

(defun-sk putnam-2010-a5-cross-coordinate-equal-p
    (x y target axis)
  (forall (epsilon)
    (implies
     (putnam-2010-a5-positive-rational-p epsilon)
     (putnam-2010-a5-cross-target-precision-p
      x y target axis epsilon))))

(defun putnam-2010-a5-cross-equals-embedding-p
    (x y target)
  (and
   (putnam-2010-a5-cross-coordinate-equal-p
    x y target 0)
   (putnam-2010-a5-cross-coordinate-equal-p
    x y target 1)
   (putnam-2010-a5-cross-coordinate-equal-p
    x y target 2)))

(defun putnam-2010-a5-zero-cross-witness-p
    (x y axis epsilon precision)
  (and
   (putnam-2010-a5-positive-rational-p precision)
   (<= precision epsilon)
   (<=
    (abs
     (putnam-2010-a5-cross-coordinate-sample
      x y axis precision))
    epsilon)))

(defun-sk putnam-2010-a5-zero-cross-precision-p
    (x y axis epsilon)
  (exists (precision)
    (putnam-2010-a5-zero-cross-witness-p
     x y axis epsilon precision)))

(defun-sk putnam-2010-a5-zero-cross-coordinate-p
    (x y axis)
  (forall (epsilon)
    (implies
     (putnam-2010-a5-positive-rational-p epsilon)
     (putnam-2010-a5-zero-cross-precision-p
      x y axis epsilon))))

(defun putnam-2010-a5-zero-cross-p (x y)
  (and
   (putnam-2010-a5-zero-cross-coordinate-p x y 0)
   (putnam-2010-a5-zero-cross-coordinate-p x y 1)
   (putnam-2010-a5-zero-cross-coordinate-p x y 2)))

(defun-sk putnam-2010-a5-cross-hypothesis-p ()
  (forall (x y)
    (implies
     (and
      (putnam-2010-a5-group-member-p x)
      (putnam-2010-a5-group-member-p y))
     (or
      (putnam-2010-a5-cross-equals-embedding-p
       x y (putnam-2010-a5-group-mul x y))
      (putnam-2010-a5-zero-cross-p x y)))))

(defun-sk putnam-2010-a5-all-cross-products-zero-p ()
  (forall (x y)
    (implies
     (and
      (putnam-2010-a5-group-member-p x)
      (putnam-2010-a5-group-member-p y))
     (putnam-2010-a5-zero-cross-p x y))))

(defun putnambench-putnam-2010-a5-statement ()
  (implies
   (and
    (putnam-2010-a5-regular-embedding-p)
    (putnam-2010-a5-embedding-injective-p)
    (putnam-2010-a5-group-p)
    (putnam-2010-a5-cross-hypothesis-p))
   (putnam-2010-a5-all-cross-products-zero-p)))

(value-triple :itpeval-statement-checked)
:q
