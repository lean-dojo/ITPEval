;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__065, "Isosceles Triangle Theorem": in an arbitrary
;; real inner-product affine space, equal apex-side lengths imply equal base
;; angles, including degenerate point configurations. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent arbitrary scalar, vector, and affine
;; point carriers.  The predicates below state all typing and structural laws
;; used to interpret them as a real ordered field, an inner-product vector
;; space, and an affine torsor; no carrier is enumerated or finite-coded.

(defstub ht065-scalar-member-p (scalar-type x) t)
(defstub ht065-vector-member-p (vector-type x) t)
(defstub ht065-point-member-p (point-type x) t)

(defstub ht065-zero-r (scalar-type) t)
(defstub ht065-one-r (scalar-type) t)
(defstub ht065-add-r (scalar-type x y) t)
(defstub ht065-mul-r (scalar-type x y) t)
(defstub ht065-opp-r (scalar-type x) t)
(defstub ht065-inv-r (scalar-type x) t)
(defstub ht065-le-r (scalar-type x y) t)

(defstub ht065-zero-v (scalar-type vector-type) t)
(defstub ht065-add-v (scalar-type vector-type x y) t)
(defstub ht065-opp-v (scalar-type vector-type x) t)
(defstub ht065-smul (scalar-type vector-type a x) t)
(defstub ht065-inner (scalar-type vector-type x y) t)

(defstub ht065-vadd
  (scalar-type vector-type point-type vector point)
  t)
(defstub ht065-vsub
  (scalar-type vector-type point-type left-point right-point)
  t)

(defun-sk ht065-point-carrier-nonempty-p (point-type)
  (exists (point)
    (ht065-point-member-p point-type point)))

(defun-sk ht065-ordered-field-laws-p (scalar-type)
  (forall (x y z)
    (implies
     (and
      (ht065-scalar-member-p scalar-type x)
      (ht065-scalar-member-p scalar-type y)
      (ht065-scalar-member-p scalar-type z))
     (let ((zero (ht065-zero-r scalar-type))
           (one (ht065-one-r scalar-type)))
       (and
        (ht065-scalar-member-p
         scalar-type (ht065-add-r scalar-type x y))
        (ht065-scalar-member-p
         scalar-type (ht065-mul-r scalar-type x y))
        (ht065-scalar-member-p
         scalar-type (ht065-opp-r scalar-type x))
        (ht065-scalar-member-p
         scalar-type (ht065-inv-r scalar-type x))

        (equal
         (ht065-add-r scalar-type x y)
         (ht065-add-r scalar-type y x))
        (equal
         (ht065-add-r
          scalar-type (ht065-add-r scalar-type x y) z)
         (ht065-add-r
          scalar-type x (ht065-add-r scalar-type y z)))
        (equal (ht065-add-r scalar-type x zero) x)
        (equal
         (ht065-add-r
          scalar-type x (ht065-opp-r scalar-type x))
         zero)

        (equal
         (ht065-mul-r scalar-type x y)
         (ht065-mul-r scalar-type y x))
        (equal
         (ht065-mul-r
          scalar-type (ht065-mul-r scalar-type x y) z)
         (ht065-mul-r
          scalar-type x (ht065-mul-r scalar-type y z)))
        (equal (ht065-mul-r scalar-type x one) x)
        (equal (ht065-mul-r scalar-type x zero) zero)
        (equal
         (ht065-mul-r
          scalar-type x (ht065-add-r scalar-type y z))
         (ht065-add-r
          scalar-type
          (ht065-mul-r scalar-type x y)
          (ht065-mul-r scalar-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (ht065-mul-r scalar-type x
                       (ht065-inv-r scalar-type x))
          one))

        (ht065-le-r scalar-type x x)
        (implies
         (and
          (ht065-le-r scalar-type x y)
          (ht065-le-r scalar-type y x))
         (equal x y))
        (implies
         (and
          (ht065-le-r scalar-type x y)
          (ht065-le-r scalar-type y z))
         (ht065-le-r scalar-type x z))
        (or
         (ht065-le-r scalar-type x y)
         (ht065-le-r scalar-type y x))
        (implies
         (ht065-le-r scalar-type x y)
         (ht065-le-r
          scalar-type
          (ht065-add-r scalar-type x z)
          (ht065-add-r scalar-type y z)))
        (implies
         (and
          (ht065-le-r scalar-type zero x)
          (ht065-le-r scalar-type zero y))
         (ht065-le-r
          scalar-type zero (ht065-mul-r scalar-type x y))))))))

(defun ht065-ordered-field-p (scalar-type)
  (and
   (ht065-scalar-member-p
    scalar-type (ht065-zero-r scalar-type))
   (ht065-scalar-member-p
    scalar-type (ht065-one-r scalar-type))
   (not
    (equal
     (ht065-zero-r scalar-type)
     (ht065-one-r scalar-type)))
   (ht065-ordered-field-laws-p scalar-type)))

(defun-sk ht065-vector-space-laws-p (scalar-type vector-type)
  (forall (a b u v w)
    (implies
     (and
      (ht065-scalar-member-p scalar-type a)
      (ht065-scalar-member-p scalar-type b)
      (ht065-vector-member-p vector-type u)
      (ht065-vector-member-p vector-type v)
      (ht065-vector-member-p vector-type w))
     (let ((one (ht065-one-r scalar-type))
           (zero-v (ht065-zero-v scalar-type vector-type)))
       (and
        (ht065-vector-member-p
         vector-type
         (ht065-add-v scalar-type vector-type u v))
        (ht065-vector-member-p
         vector-type
         (ht065-opp-v scalar-type vector-type u))
        (ht065-vector-member-p
         vector-type
         (ht065-smul scalar-type vector-type a u))

        (equal
         (ht065-add-v scalar-type vector-type u v)
         (ht065-add-v scalar-type vector-type v u))
        (equal
         (ht065-add-v
          scalar-type vector-type
          (ht065-add-v scalar-type vector-type u v)
          w)
         (ht065-add-v
          scalar-type vector-type
          u
          (ht065-add-v scalar-type vector-type v w)))
        (equal
         (ht065-add-v scalar-type vector-type u zero-v)
         u)
        (equal
         (ht065-add-v
          scalar-type vector-type
          u
          (ht065-opp-v scalar-type vector-type u))
         zero-v)

        (equal
         (ht065-smul
          scalar-type vector-type
          a
          (ht065-add-v scalar-type vector-type u v))
         (ht065-add-v
          scalar-type vector-type
          (ht065-smul scalar-type vector-type a u)
          (ht065-smul scalar-type vector-type a v)))
        (equal
         (ht065-smul
          scalar-type vector-type
          (ht065-add-r scalar-type a b)
          u)
         (ht065-add-v
          scalar-type vector-type
          (ht065-smul scalar-type vector-type a u)
          (ht065-smul scalar-type vector-type b u)))
        (equal
         (ht065-smul
          scalar-type vector-type
          (ht065-mul-r scalar-type a b)
          u)
         (ht065-smul
          scalar-type vector-type
          a
          (ht065-smul scalar-type vector-type b u)))
        (equal
         (ht065-smul scalar-type vector-type one u)
         u))))))

(defun ht065-vector-space-p (scalar-type vector-type)
  (and
   (ht065-vector-member-p
    vector-type (ht065-zero-v scalar-type vector-type))
   (ht065-vector-space-laws-p scalar-type vector-type)))

(defun-sk ht065-inner-product-laws-p (scalar-type vector-type)
  (forall (a u v w)
    (implies
     (and
      (ht065-scalar-member-p scalar-type a)
      (ht065-vector-member-p vector-type u)
      (ht065-vector-member-p vector-type v)
      (ht065-vector-member-p vector-type w))
     (let ((zero-r (ht065-zero-r scalar-type))
           (zero-v (ht065-zero-v scalar-type vector-type)))
       (and
        (ht065-scalar-member-p
         scalar-type
         (ht065-inner scalar-type vector-type u v))
        (equal
         (ht065-inner scalar-type vector-type u v)
         (ht065-inner scalar-type vector-type v u))
        (equal
         (ht065-inner
          scalar-type vector-type
          (ht065-add-v scalar-type vector-type u v)
          w)
         (ht065-add-r
          scalar-type
          (ht065-inner scalar-type vector-type u w)
          (ht065-inner scalar-type vector-type v w)))
        (equal
         (ht065-inner
          scalar-type vector-type
          (ht065-smul scalar-type vector-type a u)
          v)
         (ht065-mul-r
          scalar-type a
          (ht065-inner scalar-type vector-type u v)))
        (ht065-le-r
         scalar-type zero-r
         (ht065-inner scalar-type vector-type u u))
        (equal
         (equal
          (ht065-inner scalar-type vector-type u u)
          zero-r)
         (equal u zero-v)))))))

(defun ht065-inner-product-space-p (scalar-type vector-type)
  (and
   (ht065-ordered-field-p scalar-type)
   (ht065-vector-space-p scalar-type vector-type)
   (ht065-inner-product-laws-p scalar-type vector-type)))

(defun-sk ht065-affine-torsor-laws-p
    (scalar-type vector-type point-type)
  (forall (u v p q r)
    (implies
     (and
      (ht065-vector-member-p vector-type u)
      (ht065-vector-member-p vector-type v)
      (ht065-point-member-p point-type p)
      (ht065-point-member-p point-type q)
      (ht065-point-member-p point-type r))
     (let ((zero-v (ht065-zero-v scalar-type vector-type)))
       (and
        (ht065-point-member-p
         point-type
         (ht065-vadd
          scalar-type vector-type point-type u p))
        (ht065-vector-member-p
         vector-type
         (ht065-vsub
          scalar-type vector-type point-type p q))

        (equal
         (ht065-vadd
          scalar-type vector-type point-type zero-v p)
         p)
        (equal
         (ht065-vadd
          scalar-type vector-type point-type
          (ht065-add-v scalar-type vector-type u v)
          p)
         (ht065-vadd
          scalar-type vector-type point-type
          u
          (ht065-vadd
           scalar-type vector-type point-type v p)))
        (equal
         (ht065-vadd
          scalar-type vector-type point-type
          (ht065-vsub
           scalar-type vector-type point-type p q)
          q)
         p)
        (equal
         (ht065-vsub
          scalar-type vector-type point-type
          (ht065-vadd
           scalar-type vector-type point-type u p)
          p)
         u)
        (equal
         (ht065-vsub
          scalar-type vector-type point-type p r)
         (ht065-add-v
          scalar-type vector-type
          (ht065-vsub
           scalar-type vector-type point-type p q)
          (ht065-vsub
           scalar-type vector-type point-type q r))))))))

(defun ht065-affine-context-p
    (scalar-type vector-type point-type)
  (and
   (ht065-inner-product-space-p scalar-type vector-type)
   (ht065-point-carrier-nonempty-p point-type)
   (ht065-affine-torsor-laws-p
    scalar-type vector-type point-type)))

(defun ht065-norm-squared
    (scalar-type vector-type vector)
  (ht065-inner scalar-type vector-type vector vector))

(defun ht065-distance-equal-p
    (scalar-type vector-type point-type p q r s)
  (equal
   (ht065-norm-squared
    scalar-type vector-type
    (ht065-vsub
     scalar-type vector-type point-type p q))
   (ht065-norm-squared
    scalar-type vector-type
    (ht065-vsub
     scalar-type vector-type point-type r s))))

;; In a real inner-product space an unoriented angle lies in [0, pi], so two
;; angles are equal exactly when their cosines are equal.  The cases below
;; compare
;;
;;   <u,v> / sqrt(<u,u><v,v>)
;;
;; without introducing square roots.  A zero ray has cosine zero, matching
;; the source libraries' pi/2 convention.  For nonzero denominators, equality
;; is equivalent to equal cross-multiplied squares together with equal signs.

(defun ht065-same-sign-p (scalar-type x y)
  (let ((zero (ht065-zero-r scalar-type)))
    (or
     (and
      (ht065-le-r scalar-type zero x)
      (ht065-le-r scalar-type zero y))
     (and
      (ht065-le-r scalar-type x zero)
      (ht065-le-r scalar-type y zero)))))

(defun ht065-vector-angle-equal-p
    (scalar-type vector-type u v x y)
  (let* ((zero (ht065-zero-r scalar-type))
         (dot-uv (ht065-inner scalar-type vector-type u v))
         (dot-xy (ht065-inner scalar-type vector-type x y))
         (denom-uv-squared
          (ht065-mul-r
           scalar-type
           (ht065-norm-squared scalar-type vector-type u)
           (ht065-norm-squared scalar-type vector-type v)))
         (denom-xy-squared
          (ht065-mul-r
           scalar-type
           (ht065-norm-squared scalar-type vector-type x)
           (ht065-norm-squared scalar-type vector-type y))))
    (cond
     ((equal denom-uv-squared zero)
      (equal dot-xy zero))
     ((equal denom-xy-squared zero)
      (equal dot-uv zero))
     (t
      (and
       (ht065-same-sign-p scalar-type dot-uv dot-xy)
       (equal
        (ht065-mul-r
         scalar-type
         (ht065-mul-r scalar-type dot-uv dot-uv)
         denom-xy-squared)
        (ht065-mul-r
         scalar-type
         (ht065-mul-r scalar-type dot-xy dot-xy)
         denom-uv-squared)))))))

(defun ht065-angle-equal-p
    (scalar-type vector-type point-type
                 first-a vertex-a third-a
                 first-b vertex-b third-b)
  (ht065-vector-angle-equal-p
   scalar-type
   vector-type
   (ht065-vsub
    scalar-type vector-type point-type first-a vertex-a)
   (ht065-vsub
    scalar-type vector-type point-type third-a vertex-a)
   (ht065-vsub
    scalar-type vector-type point-type first-b vertex-b)
   (ht065-vsub
    scalar-type vector-type point-type third-b vertex-b)))

(defun-sk hundred-theorems-065-isosceles-triangle-theorem-statement
    (scalar-type vector-type point-type)
  (forall (apex base-left base-right)
    (implies
     (and
      (ht065-affine-context-p
       scalar-type vector-type point-type)
      (ht065-point-member-p point-type apex)
      (ht065-point-member-p point-type base-left)
      (ht065-point-member-p point-type base-right)
      (ht065-distance-equal-p
       scalar-type vector-type point-type
       apex base-left apex base-right))
     (ht065-angle-equal-p
      scalar-type vector-type point-type
      apex base-left base-right
      apex base-right base-left))))

(value-triple :itpeval-statement-checked)
:q
