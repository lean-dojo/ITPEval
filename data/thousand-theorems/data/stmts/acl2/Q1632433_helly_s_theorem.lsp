;; Statement-only formalization of thousand-theorems corpus artifact Q1632433,
;; "Helly's theorem": for a finite family of convex sets in a finite-dimensional
;; vector space over a linearly ordered field, if the family has at least
;; dimension plus one members and every dimension-plus-one subfamily has
;; nonempty intersection, then the whole family has nonempty intersection.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent the arbitrary index type, ordered
;; field, vector space, and set family. All carrier, algebraic, order, rank,
;; convexity, and intersection conditions are explicit in the statement.

(defstub q1632433-index-member-p (index-type index) t)
(defstub q1632433-scalar-member-p (scalar-type scalar) t)
(defstub q1632433-vector-member-p (vector-type vector) t)

(defstub q1632433-scalar-zero (scalar-type) t)
(defstub q1632433-scalar-one (scalar-type) t)
(defstub q1632433-scalar-add (scalar-type left right) t)
(defstub q1632433-scalar-multiply (scalar-type left right) t)
(defstub q1632433-scalar-negate (scalar-type scalar) t)
(defstub q1632433-scalar-inverse (scalar-type scalar) t)
(defstub q1632433-scalar-less (scalar-type left right) t)

(defstub q1632433-vector-zero (vector-type) t)
(defstub q1632433-vector-add (vector-type left right) t)
(defstub q1632433-vector-negate (vector-type vector) t)
(defstub q1632433-scalar-action
  (scalar-type vector-type scalar vector)
  t)

(defstub q1632433-family-member-p
  (index-type vector-type family-tag index vector)
  t)

;; Exact first-order laws of a nontrivial linearly ordered field.

(defun-sk q1632433-linearly-ordered-field-laws-p (scalar-type)
  (forall (x y z)
    (let ((zero (q1632433-scalar-zero scalar-type))
          (one (q1632433-scalar-one scalar-type)))
      (and
       (implies
        (q1632433-scalar-member-p scalar-type x)
        (and
         (q1632433-scalar-member-p
          scalar-type
          (q1632433-scalar-negate scalar-type x))
         (q1632433-scalar-member-p
          scalar-type
          (q1632433-scalar-inverse scalar-type x))
         (equal
          (q1632433-scalar-add scalar-type x zero)
          x)
         (equal
          (q1632433-scalar-add
           scalar-type x
           (q1632433-scalar-negate scalar-type x))
          zero)
         (equal
          (q1632433-scalar-multiply scalar-type x one)
          x)
         (implies
          (not (equal x zero))
          (equal
           (q1632433-scalar-multiply
            scalar-type x
            (q1632433-scalar-inverse scalar-type x))
           one))
         (not (q1632433-scalar-less scalar-type x x))))
       (implies
        (and
         (q1632433-scalar-member-p scalar-type x)
         (q1632433-scalar-member-p scalar-type y))
        (and
         (q1632433-scalar-member-p
          scalar-type
          (q1632433-scalar-add scalar-type x y))
         (q1632433-scalar-member-p
          scalar-type
          (q1632433-scalar-multiply scalar-type x y))
         (equal
          (q1632433-scalar-add scalar-type x y)
          (q1632433-scalar-add scalar-type y x))
         (equal
          (q1632433-scalar-multiply scalar-type x y)
          (q1632433-scalar-multiply scalar-type y x))
         (or
          (q1632433-scalar-less scalar-type x y)
          (equal x y)
          (q1632433-scalar-less scalar-type y x))))
       (implies
        (and
         (q1632433-scalar-member-p scalar-type x)
         (q1632433-scalar-member-p scalar-type y)
         (q1632433-scalar-member-p scalar-type z))
        (and
         (equal
          (q1632433-scalar-add
           scalar-type
           (q1632433-scalar-add scalar-type x y)
           z)
          (q1632433-scalar-add
           scalar-type
           x
           (q1632433-scalar-add scalar-type y z)))
         (equal
          (q1632433-scalar-multiply
           scalar-type
           (q1632433-scalar-multiply scalar-type x y)
           z)
          (q1632433-scalar-multiply
           scalar-type
           x
           (q1632433-scalar-multiply scalar-type y z)))
         (equal
          (q1632433-scalar-multiply
           scalar-type
           x
           (q1632433-scalar-add scalar-type y z))
          (q1632433-scalar-add
           scalar-type
           (q1632433-scalar-multiply scalar-type x y)
           (q1632433-scalar-multiply scalar-type x z)))
         (implies
          (and
           (q1632433-scalar-less scalar-type x y)
           (q1632433-scalar-less scalar-type y z))
          (q1632433-scalar-less scalar-type x z))
         (implies
          (q1632433-scalar-less scalar-type x y)
          (q1632433-scalar-less
           scalar-type
           (q1632433-scalar-add scalar-type x z)
           (q1632433-scalar-add scalar-type y z)))
         (implies
          (and
           (q1632433-scalar-less scalar-type zero x)
           (q1632433-scalar-less scalar-type zero y))
          (q1632433-scalar-less
           scalar-type
           zero
           (q1632433-scalar-multiply scalar-type x y)))))))))

(defun q1632433-linearly-ordered-field-p (scalar-type)
  (let ((zero (q1632433-scalar-zero scalar-type))
        (one (q1632433-scalar-one scalar-type)))
    (and
     (q1632433-scalar-member-p scalar-type zero)
     (q1632433-scalar-member-p scalar-type one)
     (not (equal zero one))
     (equal
      (q1632433-scalar-inverse scalar-type zero)
      zero)
     (q1632433-linearly-ordered-field-laws-p scalar-type))))

;; Exact additive-commutative-group and module laws.

(defun-sk q1632433-module-laws-p (scalar-type vector-type)
  (forall (a b x y z)
    (let ((scalar-zero (q1632433-scalar-zero scalar-type))
          (scalar-one (q1632433-scalar-one scalar-type))
          (vector-zero (q1632433-vector-zero vector-type)))
      (and
       (implies
        (q1632433-vector-member-p vector-type x)
        (and
         (q1632433-vector-member-p
          vector-type
          (q1632433-vector-negate vector-type x))
         (equal
          (q1632433-vector-add vector-type x vector-zero)
          x)
         (equal
          (q1632433-vector-add
           vector-type x
           (q1632433-vector-negate vector-type x))
          vector-zero)
         (equal
          (q1632433-scalar-action
           scalar-type vector-type scalar-one x)
          x)
         (equal
          (q1632433-scalar-action
           scalar-type vector-type scalar-zero x)
          vector-zero)))
       (implies
        (and
         (q1632433-vector-member-p vector-type x)
         (q1632433-vector-member-p vector-type y))
        (and
         (q1632433-vector-member-p
          vector-type
          (q1632433-vector-add vector-type x y))
         (equal
          (q1632433-vector-add vector-type x y)
          (q1632433-vector-add vector-type y x))))
       (implies
        (and
         (q1632433-vector-member-p vector-type x)
         (q1632433-vector-member-p vector-type y)
         (q1632433-vector-member-p vector-type z))
        (equal
         (q1632433-vector-add
          vector-type
          (q1632433-vector-add vector-type x y)
          z)
         (q1632433-vector-add
          vector-type
          x
          (q1632433-vector-add vector-type y z))))
       (implies
        (and
         (q1632433-scalar-member-p scalar-type a)
         (q1632433-vector-member-p vector-type x))
        (q1632433-vector-member-p
         vector-type
         (q1632433-scalar-action
          scalar-type vector-type a x)))
       (implies
        (q1632433-scalar-member-p scalar-type a)
        (equal
         (q1632433-scalar-action
          scalar-type vector-type a vector-zero)
         vector-zero))
       (implies
        (and
         (q1632433-scalar-member-p scalar-type a)
         (q1632433-vector-member-p vector-type x)
         (q1632433-vector-member-p vector-type y))
        (equal
         (q1632433-scalar-action
          scalar-type vector-type a
          (q1632433-vector-add vector-type x y))
         (q1632433-vector-add
          vector-type
          (q1632433-scalar-action
           scalar-type vector-type a x)
          (q1632433-scalar-action
           scalar-type vector-type a y))))
       (implies
        (and
         (q1632433-scalar-member-p scalar-type a)
         (q1632433-scalar-member-p scalar-type b)
         (q1632433-vector-member-p vector-type x))
        (and
         (equal
          (q1632433-scalar-action
           scalar-type vector-type
           (q1632433-scalar-add scalar-type a b)
           x)
          (q1632433-vector-add
           vector-type
           (q1632433-scalar-action
            scalar-type vector-type a x)
           (q1632433-scalar-action
            scalar-type vector-type b x)))
         (equal
          (q1632433-scalar-action
           scalar-type vector-type
           (q1632433-scalar-multiply scalar-type a b)
           x)
          (q1632433-scalar-action
           scalar-type vector-type
           a
           (q1632433-scalar-action
            scalar-type vector-type b x)))))))))

(defun q1632433-module-p (scalar-type vector-type)
  (and
   (q1632433-vector-member-p
    vector-type
    (q1632433-vector-zero vector-type))
   (q1632433-module-laws-p scalar-type vector-type)))

;; Finite-dimensionality of exact rank DIMENSION is the internal existence of
;; a finite linearly independent spanning list of that length.

(defun q1632433-scalar-list-p (scalar-type values)
  (if (consp values)
      (and
       (q1632433-scalar-member-p scalar-type (car values))
       (q1632433-scalar-list-p scalar-type (cdr values)))
    (equal values nil)))

(defun q1632433-vector-list-p (vector-type values)
  (if (consp values)
      (and
       (q1632433-vector-member-p vector-type (car values))
       (q1632433-vector-list-p vector-type (cdr values)))
    (equal values nil)))

(defun q1632433-all-zero-coefficients-p
    (scalar-type coefficients)
  (if (consp coefficients)
      (and
       (equal
        (car coefficients)
        (q1632433-scalar-zero scalar-type))
       (q1632433-all-zero-coefficients-p
        scalar-type (cdr coefficients)))
    (equal coefficients nil)))

(defun q1632433-linear-combination
    (scalar-type vector-type basis coefficients)
  (if (and (consp basis) (consp coefficients))
      (q1632433-vector-add
       vector-type
       (q1632433-scalar-action
        scalar-type vector-type
        (car coefficients) (car basis))
       (q1632433-linear-combination
        scalar-type vector-type
        (cdr basis) (cdr coefficients)))
    (q1632433-vector-zero vector-type)))

(defun-sk q1632433-basis-coefficients-exist-p
    (scalar-type vector-type basis vector)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (equal (len coefficients) (len basis))
     (q1632433-scalar-list-p scalar-type coefficients)
     (equal
      (q1632433-linear-combination
       scalar-type vector-type basis coefficients)
      vector))))

(defun-sk q1632433-basis-spans-p
    (scalar-type vector-type basis)
  (forall (vector)
    (implies
     (q1632433-vector-member-p vector-type vector)
     (q1632433-basis-coefficients-exist-p
      scalar-type vector-type basis vector))))

(defun-sk q1632433-basis-independent-p
    (scalar-type vector-type basis)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (equal (len coefficients) (len basis))
      (q1632433-scalar-list-p scalar-type coefficients)
      (equal
       (q1632433-linear-combination
        scalar-type vector-type basis coefficients)
       (q1632433-vector-zero vector-type)))
     (q1632433-all-zero-coefficients-p
      scalar-type coefficients))))

(defun q1632433-basis-p
    (scalar-type vector-type basis)
  (and
   (true-listp basis)
   (no-duplicatesp-equal basis)
   (q1632433-vector-list-p vector-type basis)
   (q1632433-basis-spans-p scalar-type vector-type basis)
   (q1632433-basis-independent-p
    scalar-type vector-type basis)))

(defun-sk q1632433-finite-dimensional-rank-p
    (scalar-type vector-type dimension)
  (exists (basis)
    (and
     (natp dimension)
     (q1632433-basis-p scalar-type vector-type basis)
     (equal (len basis) dimension))))

;; Finite index lists represent source Finsets without changing their carrier.

(defun q1632433-index-list-p (index-type indices)
  (if (consp indices)
      (and
       (q1632433-index-member-p index-type (car indices))
       (q1632433-index-list-p index-type (cdr indices)))
    (equal indices nil)))

(defun q1632433-subset-list-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (q1632433-subset-list-p (cdr left) right))
    (equal left nil)))

(defun q1632433-subfamily-p
    (index-type subfamily family-indices)
  (and
   (true-listp subfamily)
   (no-duplicatesp-equal subfamily)
   (q1632433-index-list-p index-type subfamily)
   (q1632433-subset-list-p subfamily family-indices)))

;; Convexity is closure under every nonnegative binary affine combination.

(defun-sk q1632433-family-convex-on-p
    (index-type scalar-type vector-type family-tag family-indices)
  (forall (index a b x y)
    (implies
     (and
      (member-equal index family-indices)
      (q1632433-index-member-p index-type index)
      (q1632433-scalar-member-p scalar-type a)
      (q1632433-scalar-member-p scalar-type b)
      (q1632433-vector-member-p vector-type x)
      (q1632433-vector-member-p vector-type y)
      (q1632433-family-member-p
       index-type vector-type family-tag index x)
      (q1632433-family-member-p
       index-type vector-type family-tag index y)
      (not
       (q1632433-scalar-less
        scalar-type a
        (q1632433-scalar-zero scalar-type)))
      (not
       (q1632433-scalar-less
        scalar-type b
        (q1632433-scalar-zero scalar-type)))
      (equal
       (q1632433-scalar-add scalar-type a b)
       (q1632433-scalar-one scalar-type)))
     (q1632433-family-member-p
      index-type vector-type family-tag index
      (q1632433-vector-add
       vector-type
       (q1632433-scalar-action
        scalar-type vector-type a x)
       (q1632433-scalar-action
        scalar-type vector-type b y))))))

;; Nonempty intersections keep their point witnesses existentially internal.

(defun q1632433-point-in-all-p
    (index-type vector-type family-tag indices point)
  (if (consp indices)
      (and
       (q1632433-family-member-p
        index-type vector-type family-tag
        (car indices) point)
       (q1632433-point-in-all-p
        index-type vector-type family-tag
        (cdr indices) point))
    (equal indices nil)))

(defun-sk q1632433-intersection-nonempty-p
    (index-type vector-type family-tag indices)
  (exists (point)
    (and
     (q1632433-vector-member-p vector-type point)
     (q1632433-point-in-all-p
      index-type vector-type family-tag indices point))))

(defun-sk q1632433-critical-intersections-nonempty-p
    (index-type vector-type family-tag family-indices dimension)
  (forall (subfamily)
    (implies
     (and
      (q1632433-subfamily-p
       index-type subfamily family-indices)
      (equal (len subfamily) (+ dimension 1)))
     (q1632433-intersection-nonempty-p
      index-type vector-type family-tag subfamily))))

(defun-sk thousand-theorems-q1632433-helly-s-theorem-statement ()
  (forall
    (index-type scalar-type vector-type family-tag
     family-indices dimension)
    (implies
     (and
      (q1632433-linearly-ordered-field-p scalar-type)
      (q1632433-module-p scalar-type vector-type)
      (q1632433-finite-dimensional-rank-p
       scalar-type vector-type dimension)
      (true-listp family-indices)
      (no-duplicatesp-equal family-indices)
      (q1632433-index-list-p index-type family-indices)
      (<= (+ dimension 1) (len family-indices))
      (q1632433-family-convex-on-p
       index-type scalar-type vector-type
       family-tag family-indices)
      (q1632433-critical-intersections-nonempty-p
       index-type vector-type family-tag
       family-indices dimension))
     (q1632433-intersection-nonempty-p
      index-type vector-type family-tag family-indices))))

(value-triple :itpeval-statement-checked)
:q
