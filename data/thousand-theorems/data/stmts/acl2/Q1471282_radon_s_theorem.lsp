;; Statement-only formalization of thousand-theorems corpus artifact Q1471282
;; (thousand-theorems__acl2__Q1471282), "Radon's theorem": every
;; affine-dependent family over a linearly ordered field has complementary
;; parts whose image convex hulls intersect. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic interfaces represent the arbitrary index type,
;; linearly ordered field, module, and indexed family. Every typing and
;; algebraic law used by the source typeclasses is explicit below.

(defstub q1471282-index-member-p (index-type index) t)
(defstub q1471282-scalar-member-p (scalar-type scalar) t)
(defstub q1471282-vector-member-p (vector-type vector) t)

(defstub q1471282-scalar-zero (scalar-type) t)
(defstub q1471282-scalar-one (scalar-type) t)
(defstub q1471282-scalar-add (scalar-type left right) t)
(defstub q1471282-scalar-multiply (scalar-type left right) t)
(defstub q1471282-scalar-negate (scalar-type scalar) t)
(defstub q1471282-scalar-inverse (scalar-type scalar) t)
(defstub q1471282-scalar-less (scalar-type left right) t)

(defstub q1471282-vector-zero (vector-type) t)
(defstub q1471282-vector-add (vector-type left right) t)
(defstub q1471282-vector-negate (vector-type vector) t)
(defstub q1471282-scalar-action
  (scalar-type vector-type scalar vector)
  t)

(defstub q1471282-family-value
  (index-type vector-type family-tag index)
  t)

;; Exact first-order laws of a nontrivial linearly ordered field.

(defun-sk q1471282-linearly-ordered-field-laws-p (scalar-type)
  (forall (x y z)
    (let ((zero (q1471282-scalar-zero scalar-type))
          (one (q1471282-scalar-one scalar-type)))
      (and
       (implies
        (q1471282-scalar-member-p scalar-type x)
        (and
         (q1471282-scalar-member-p
          scalar-type
          (q1471282-scalar-negate scalar-type x))
         (q1471282-scalar-member-p
          scalar-type
          (q1471282-scalar-inverse scalar-type x))
         (equal
          (q1471282-scalar-add scalar-type x zero)
          x)
         (equal
          (q1471282-scalar-add
           scalar-type x
           (q1471282-scalar-negate scalar-type x))
          zero)
         (equal
          (q1471282-scalar-multiply scalar-type x one)
          x)
         (implies
          (not (equal x zero))
          (equal
           (q1471282-scalar-multiply
            scalar-type x
            (q1471282-scalar-inverse scalar-type x))
           one))
         (not (q1471282-scalar-less scalar-type x x))))
       (implies
        (and
         (q1471282-scalar-member-p scalar-type x)
         (q1471282-scalar-member-p scalar-type y))
        (and
         (q1471282-scalar-member-p
          scalar-type
          (q1471282-scalar-add scalar-type x y))
         (q1471282-scalar-member-p
          scalar-type
          (q1471282-scalar-multiply scalar-type x y))
         (equal
          (q1471282-scalar-add scalar-type x y)
          (q1471282-scalar-add scalar-type y x))
         (equal
          (q1471282-scalar-multiply scalar-type x y)
          (q1471282-scalar-multiply scalar-type y x))
         (or
          (q1471282-scalar-less scalar-type x y)
          (equal x y)
          (q1471282-scalar-less scalar-type y x))))
       (implies
        (and
         (q1471282-scalar-member-p scalar-type x)
         (q1471282-scalar-member-p scalar-type y)
         (q1471282-scalar-member-p scalar-type z))
        (and
         (equal
          (q1471282-scalar-add
           scalar-type
           (q1471282-scalar-add scalar-type x y)
           z)
          (q1471282-scalar-add
           scalar-type
           x
           (q1471282-scalar-add scalar-type y z)))
         (equal
          (q1471282-scalar-multiply
           scalar-type
           (q1471282-scalar-multiply scalar-type x y)
           z)
          (q1471282-scalar-multiply
           scalar-type
           x
           (q1471282-scalar-multiply scalar-type y z)))
         (equal
          (q1471282-scalar-multiply
           scalar-type
           x
           (q1471282-scalar-add scalar-type y z))
          (q1471282-scalar-add
           scalar-type
           (q1471282-scalar-multiply scalar-type x y)
           (q1471282-scalar-multiply scalar-type x z)))
         (implies
          (and
           (q1471282-scalar-less scalar-type x y)
           (q1471282-scalar-less scalar-type y z))
          (q1471282-scalar-less scalar-type x z))
         (implies
          (q1471282-scalar-less scalar-type x y)
          (q1471282-scalar-less
           scalar-type
           (q1471282-scalar-add scalar-type x z)
           (q1471282-scalar-add scalar-type y z)))
         (implies
          (and
           (q1471282-scalar-less scalar-type zero x)
           (q1471282-scalar-less scalar-type zero y))
          (q1471282-scalar-less
           scalar-type
           zero
           (q1471282-scalar-multiply scalar-type x y)))))))))

(defun q1471282-linearly-ordered-field-p (scalar-type)
  (let ((zero (q1471282-scalar-zero scalar-type))
        (one (q1471282-scalar-one scalar-type)))
    (and
     (q1471282-scalar-member-p scalar-type zero)
     (q1471282-scalar-member-p scalar-type one)
     (not (equal zero one))
     (equal
      (q1471282-scalar-inverse scalar-type zero)
      zero)
     (q1471282-linearly-ordered-field-laws-p scalar-type))))

;; Exact additive-commutative-group and module laws.

(defun-sk q1471282-module-laws-p (scalar-type vector-type)
  (forall (a b x y z)
    (let ((vector-zero (q1471282-vector-zero vector-type)))
      (and
       (implies
        (q1471282-vector-member-p vector-type x)
        (and
         (q1471282-vector-member-p
          vector-type
          (q1471282-vector-negate vector-type x))
         (equal
          (q1471282-vector-add vector-type x vector-zero)
          x)
         (equal
          (q1471282-vector-add
           vector-type x
           (q1471282-vector-negate vector-type x))
          vector-zero)
         (equal
          (q1471282-scalar-action
           scalar-type vector-type
           (q1471282-scalar-one scalar-type)
           x)
          x)))
       (implies
        (and
         (q1471282-vector-member-p vector-type x)
         (q1471282-vector-member-p vector-type y))
        (and
         (q1471282-vector-member-p
          vector-type
          (q1471282-vector-add vector-type x y))
         (equal
          (q1471282-vector-add vector-type x y)
          (q1471282-vector-add vector-type y x))))
       (implies
        (and
         (q1471282-vector-member-p vector-type x)
         (q1471282-vector-member-p vector-type y)
         (q1471282-vector-member-p vector-type z))
        (equal
         (q1471282-vector-add
          vector-type
          (q1471282-vector-add vector-type x y)
          z)
         (q1471282-vector-add
          vector-type
          x
          (q1471282-vector-add vector-type y z))))
       (implies
        (and
         (q1471282-scalar-member-p scalar-type a)
         (q1471282-vector-member-p vector-type x))
        (q1471282-vector-member-p
         vector-type
         (q1471282-scalar-action
          scalar-type vector-type a x)))
       (implies
        (and
         (q1471282-scalar-member-p scalar-type a)
         (q1471282-vector-member-p vector-type x)
         (q1471282-vector-member-p vector-type y))
        (equal
         (q1471282-scalar-action
          scalar-type vector-type a
          (q1471282-vector-add vector-type x y))
         (q1471282-vector-add
          vector-type
          (q1471282-scalar-action
           scalar-type vector-type a x)
          (q1471282-scalar-action
           scalar-type vector-type a y))))
       (implies
        (and
         (q1471282-scalar-member-p scalar-type a)
         (q1471282-scalar-member-p scalar-type b)
         (q1471282-vector-member-p vector-type x))
        (and
         (equal
          (q1471282-scalar-action
           scalar-type vector-type
           (q1471282-scalar-add scalar-type a b)
           x)
          (q1471282-vector-add
           vector-type
           (q1471282-scalar-action
            scalar-type vector-type a x)
           (q1471282-scalar-action
            scalar-type vector-type b x)))
         (equal
          (q1471282-scalar-action
           scalar-type vector-type
           (q1471282-scalar-multiply scalar-type a b)
           x)
          (q1471282-scalar-action
           scalar-type vector-type
           a
           (q1471282-scalar-action
            scalar-type vector-type b x)))))))))

(defun q1471282-module-p (scalar-type vector-type)
  (and
   (q1471282-vector-member-p
    vector-type
    (q1471282-vector-zero vector-type))
   (q1471282-module-laws-p scalar-type vector-type)))

(defun-sk q1471282-family-p
    (index-type vector-type family-tag)
  (forall (index)
    (implies
     (q1471282-index-member-p index-type index)
     (q1471282-vector-member-p
      vector-type
      (q1471282-family-value
       index-type vector-type family-tag index)))))

;; Affine dependence is represented by its exact finite-support
;; characterization: nonzero scalar coefficients summing to zero whose
;; weighted family sum is the zero vector.

(defun q1471282-index-weight-lists-p
    (index-type scalar-type support weights)
  (if (consp support)
      (and
       (consp weights)
       (q1471282-index-member-p index-type (car support))
       (q1471282-scalar-member-p scalar-type (car weights))
       (q1471282-index-weight-lists-p
        index-type scalar-type
        (cdr support) (cdr weights)))
    (and
     (equal support nil)
     (equal weights nil))))

(defun q1471282-has-nonzero-weight-p
    (scalar-type weights)
  (if (consp weights)
      (or
       (not
        (equal
         (car weights)
         (q1471282-scalar-zero scalar-type)))
       (q1471282-has-nonzero-weight-p
        scalar-type (cdr weights)))
    nil))

(defun q1471282-scalar-sum (scalar-type weights)
  (if (consp weights)
      (q1471282-scalar-add
       scalar-type
       (car weights)
       (q1471282-scalar-sum scalar-type (cdr weights)))
    (q1471282-scalar-zero scalar-type)))

(defun q1471282-weighted-family-sum
    (index-type scalar-type vector-type family-tag support weights)
  (if (consp support)
      (q1471282-vector-add
       vector-type
       (q1471282-scalar-action
        scalar-type vector-type
        (car weights)
        (q1471282-family-value
         index-type vector-type family-tag (car support)))
       (q1471282-weighted-family-sum
        index-type scalar-type vector-type family-tag
        (cdr support) (cdr weights)))
    (q1471282-vector-zero vector-type)))

(defun q1471282-affine-relation-p
    (index-type scalar-type vector-type family-tag support weights)
  (and
   (q1471282-index-weight-lists-p
    index-type scalar-type support weights)
   (no-duplicatesp-equal support)
   (q1471282-has-nonzero-weight-p scalar-type weights)
   (equal
    (q1471282-scalar-sum scalar-type weights)
    (q1471282-scalar-zero scalar-type))
   (equal
    (q1471282-weighted-family-sum
     index-type scalar-type vector-type family-tag support weights)
    (q1471282-vector-zero vector-type))))

(defun-sk q1471282-affine-dependent-p
    (index-type scalar-type vector-type family-tag)
  (exists (support weights)
    (q1471282-affine-relation-p
     index-type scalar-type vector-type family-tag support weights)))

;; Convex-hull membership is exactly a finite nonnegative affine
;; combination. Two disjoint supports are equivalent to supports lying in a
;; subset and its complement: use the left support as the subset in one
;; direction, and extract the two finite supports from convex combinations in
;; the other.

(defun q1471282-nonnegative-weights-p
    (scalar-type weights)
  (if (consp weights)
      (and
       (not
        (q1471282-scalar-less
         scalar-type
         (car weights)
         (q1471282-scalar-zero scalar-type)))
       (q1471282-nonnegative-weights-p
        scalar-type (cdr weights)))
    (equal weights nil)))

(defun q1471282-convex-combination-p
    (index-type scalar-type vector-type family-tag
     support weights point)
  (and
   (q1471282-vector-member-p vector-type point)
   (q1471282-index-weight-lists-p
    index-type scalar-type support weights)
   (no-duplicatesp-equal support)
   (q1471282-nonnegative-weights-p scalar-type weights)
   (equal
    (q1471282-scalar-sum scalar-type weights)
    (q1471282-scalar-one scalar-type))
   (equal
    (q1471282-weighted-family-sum
     index-type scalar-type vector-type family-tag support weights)
    point)))

(defun q1471282-disjoint-supports-p (left right)
  (if (consp left)
      (and
       (not (member-equal (car left) right))
       (q1471282-disjoint-supports-p (cdr left) right))
    (equal left nil)))

(defun-sk q1471282-radon-partition-exists-p
    (index-type scalar-type vector-type family-tag)
  (exists
    (left-support left-weights
     right-support right-weights point)
    (and
     (q1471282-convex-combination-p
      index-type scalar-type vector-type family-tag
      left-support left-weights point)
     (q1471282-convex-combination-p
      index-type scalar-type vector-type family-tag
      right-support right-weights point)
     (q1471282-disjoint-supports-p
      left-support right-support))))

(defun-sk thousand-theorems-q1471282-radon-s-theorem-statement ()
  (forall (index-type scalar-type vector-type family-tag)
    (implies
     (and
      (q1471282-linearly-ordered-field-p scalar-type)
      (q1471282-module-p scalar-type vector-type)
      (q1471282-family-p index-type vector-type family-tag)
      (q1471282-affine-dependent-p
       index-type scalar-type vector-type family-tag))
     (q1471282-radon-partition-exists-p
      index-type scalar-type vector-type family-tag))))

(value-triple :itpeval-statement-checked)
:q
