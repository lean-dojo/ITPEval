;; Statement-only formalization of thousand-theorems corpus artifact Q11518,
;; "Pythagorean theorem": for three arbitrary points in a real inner-product
;; affine space, the squared-distance identity holds exactly when the angle at
;; the middle point is a right angle. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols present the source's real scalar field,
;; arbitrary real inner-product space, and arbitrary affine torsor. Every
;; carrier restriction and structural law used by the source typeclasses is
;; explicit in the statement context.

(defstub q11518-scalar-member-p (real-type x) t)
(defstub q11518-vector-member-p (vector-type x) t)
(defstub q11518-point-member-p (point-type x) t)

(defstub q11518-zero-r (real-type) t)
(defstub q11518-one-r (real-type) t)
(defstub q11518-add-r (real-type x y) t)
(defstub q11518-mul-r (real-type x y) t)
(defstub q11518-neg-r (real-type x) t)
(defstub q11518-inv-r (real-type x) t)
(defstub q11518-le-r (real-type x y) t)

(defstub q11518-zero-v (real-type vector-type) t)
(defstub q11518-add-v (real-type vector-type x y) t)
(defstub q11518-neg-v (real-type vector-type x) t)
(defstub q11518-smul (real-type vector-type a x) t)
(defstub q11518-inner (real-type vector-type x y) t)

(defstub q11518-origin (point-type) t)
(defstub q11518-vadd (real-type vector-type point-type v p) t)
(defstub q11518-vsub (real-type vector-type point-type p q) t)

(defun-sk q11518-real-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q11518-scalar-member-p real-type x)
      (q11518-scalar-member-p real-type y)
      (q11518-scalar-member-p real-type z))
     (let ((zero (q11518-zero-r real-type))
           (one (q11518-one-r real-type)))
       (and
        (q11518-scalar-member-p
         real-type (q11518-add-r real-type x y))
        (q11518-scalar-member-p
         real-type (q11518-mul-r real-type x y))
        (q11518-scalar-member-p
         real-type (q11518-neg-r real-type x))
        (q11518-scalar-member-p
         real-type (q11518-inv-r real-type x))

        (equal
         (q11518-add-r
          real-type (q11518-add-r real-type x y) z)
         (q11518-add-r
          real-type x (q11518-add-r real-type y z)))
        (equal (q11518-add-r real-type x y)
               (q11518-add-r real-type y x))
        (equal (q11518-add-r real-type x zero) x)
        (equal
         (q11518-add-r
          real-type x (q11518-neg-r real-type x))
         zero)

        (equal
         (q11518-mul-r
          real-type (q11518-mul-r real-type x y) z)
         (q11518-mul-r
          real-type x (q11518-mul-r real-type y z)))
        (equal (q11518-mul-r real-type x y)
               (q11518-mul-r real-type y x))
        (equal (q11518-mul-r real-type x one) x)
        (equal
         (q11518-mul-r
          real-type x (q11518-add-r real-type y z))
         (q11518-add-r
          real-type
          (q11518-mul-r real-type x y)
          (q11518-mul-r real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (q11518-mul-r
           real-type x (q11518-inv-r real-type x))
          one))

        (q11518-le-r real-type x x)
        (implies
         (and
          (q11518-le-r real-type x y)
          (q11518-le-r real-type y x))
         (equal x y))
        (implies
         (and
          (q11518-le-r real-type x y)
          (q11518-le-r real-type y z))
         (q11518-le-r real-type x z))
        (or
         (q11518-le-r real-type x y)
         (q11518-le-r real-type y x))
        (implies
         (q11518-le-r real-type x y)
         (q11518-le-r
          real-type
          (q11518-add-r real-type x z)
          (q11518-add-r real-type y z)))
        (implies
         (and
          (q11518-le-r real-type zero x)
          (q11518-le-r real-type zero y))
         (q11518-le-r
          real-type zero (q11518-mul-r real-type x y))))))))

(defun q11518-real-field-p (real-type)
  (let ((zero (q11518-zero-r real-type))
        (one (q11518-one-r real-type)))
    (and
     (q11518-scalar-member-p real-type zero)
     (q11518-scalar-member-p real-type one)
     (not (equal zero one))
     (q11518-le-r real-type zero one)
     (q11518-real-field-laws-p real-type))))

(defun-sk q11518-vector-space-laws-p (real-type vector-type)
  (forall (a b u v w)
    (implies
     (and
      (q11518-scalar-member-p real-type a)
      (q11518-scalar-member-p real-type b)
      (q11518-vector-member-p vector-type u)
      (q11518-vector-member-p vector-type v)
      (q11518-vector-member-p vector-type w))
     (let ((zero-v (q11518-zero-v real-type vector-type))
           (one-r (q11518-one-r real-type)))
       (and
        (q11518-vector-member-p
         vector-type (q11518-add-v real-type vector-type u v))
        (q11518-vector-member-p
         vector-type (q11518-neg-v real-type vector-type u))
        (q11518-vector-member-p
         vector-type (q11518-smul real-type vector-type a u))

        (equal
         (q11518-add-v
          real-type vector-type
          (q11518-add-v real-type vector-type u v)
          w)
         (q11518-add-v
          real-type vector-type
          u
          (q11518-add-v real-type vector-type v w)))
        (equal
         (q11518-add-v real-type vector-type u v)
         (q11518-add-v real-type vector-type v u))
        (equal
         (q11518-add-v real-type vector-type u zero-v)
         u)
        (equal
         (q11518-add-v
          real-type vector-type
          u
          (q11518-neg-v real-type vector-type u))
         zero-v)

        (equal
         (q11518-smul real-type vector-type one-r u)
         u)
        (equal
         (q11518-smul
          real-type vector-type
          (q11518-mul-r real-type a b)
          u)
         (q11518-smul
          real-type vector-type
          a
          (q11518-smul real-type vector-type b u)))
        (equal
         (q11518-smul
          real-type vector-type
          (q11518-add-r real-type a b)
          u)
         (q11518-add-v
          real-type vector-type
          (q11518-smul real-type vector-type a u)
          (q11518-smul real-type vector-type b u)))
        (equal
         (q11518-smul
          real-type vector-type
          a
          (q11518-add-v real-type vector-type u v))
         (q11518-add-v
          real-type vector-type
          (q11518-smul real-type vector-type a u)
          (q11518-smul real-type vector-type a v))))))))

(defun q11518-vector-space-p (real-type vector-type)
  (and
   (q11518-vector-member-p
    vector-type (q11518-zero-v real-type vector-type))
   (q11518-vector-space-laws-p real-type vector-type)))

(defun-sk q11518-inner-product-laws-p (real-type vector-type)
  (forall (a u v w)
    (implies
     (and
      (q11518-scalar-member-p real-type a)
      (q11518-vector-member-p vector-type u)
      (q11518-vector-member-p vector-type v)
      (q11518-vector-member-p vector-type w))
     (let ((zero-r (q11518-zero-r real-type))
           (zero-v (q11518-zero-v real-type vector-type)))
       (and
        (q11518-scalar-member-p
         real-type (q11518-inner real-type vector-type u v))
        (equal
         (q11518-inner
          real-type vector-type
          (q11518-add-v real-type vector-type u v)
          w)
         (q11518-add-r
          real-type
          (q11518-inner real-type vector-type u w)
          (q11518-inner real-type vector-type v w)))
        (equal
         (q11518-inner
          real-type vector-type
          (q11518-smul real-type vector-type a u)
          v)
         (q11518-mul-r
          real-type
          a
          (q11518-inner real-type vector-type u v)))
        (equal
         (q11518-inner real-type vector-type u v)
         (q11518-inner real-type vector-type v u))
        (q11518-le-r
         real-type
         zero-r
         (q11518-inner real-type vector-type u u))
        (iff
         (equal
          (q11518-inner real-type vector-type u u)
          zero-r)
         (equal u zero-v)))))))

(defun-sk q11518-affine-torsor-laws-p
    (real-type vector-type point-type)
  (forall (p q u v)
    (implies
     (and
      (q11518-point-member-p point-type p)
      (q11518-point-member-p point-type q)
      (q11518-vector-member-p vector-type u)
      (q11518-vector-member-p vector-type v))
     (let ((zero-v (q11518-zero-v real-type vector-type)))
       (and
        (q11518-point-member-p
         point-type
         (q11518-vadd
          real-type vector-type point-type u p))
        (q11518-vector-member-p
         vector-type
         (q11518-vsub
          real-type vector-type point-type p q))
        (equal
         (q11518-vadd
          real-type vector-type point-type zero-v p)
         p)
        (equal
         (q11518-vadd
          real-type vector-type point-type
          (q11518-add-v real-type vector-type u v)
          p)
         (q11518-vadd
          real-type vector-type point-type
          u
          (q11518-vadd
           real-type vector-type point-type v p)))
        (equal
         (q11518-vadd
          real-type vector-type point-type
          (q11518-vsub
           real-type vector-type point-type p q)
          q)
         p)
        (equal
         (q11518-vsub
          real-type vector-type point-type
          (q11518-vadd
           real-type vector-type point-type u p)
          p)
         u))))))

(defun q11518-context-p (real-type vector-type point-type)
  (and
   (q11518-real-field-p real-type)
   (q11518-vector-space-p real-type vector-type)
   (q11518-inner-product-laws-p real-type vector-type)
   (q11518-point-member-p
    point-type (q11518-origin point-type))
   (q11518-affine-torsor-laws-p
    real-type vector-type point-type)))

;; In the source real inner-product geometry, dist(p,q)^2 is
;; <p-q,p-q>, and angle(p1,p2,p3)=pi/2 is equivalent in both directions to
;; <p1-p2,p3-p2>=0, including degenerate rays. These definitions therefore
;; eliminate only derived norm, distance, and angle notation.

(defun q11518-distance-squared
    (real-type vector-type point-type p q)
  (let ((difference
         (q11518-vsub
          real-type vector-type point-type p q)))
    (q11518-inner
     real-type vector-type difference difference)))

(defun q11518-right-angle-p
    (real-type vector-type point-type p1 p2 p3)
  (equal
   (q11518-inner
    real-type
    vector-type
    (q11518-vsub
     real-type vector-type point-type p1 p2)
    (q11518-vsub
     real-type vector-type point-type p3 p2))
   (q11518-zero-r real-type)))

(defun-sk thousand-theorems-q11518-pythagorean-theorem-statement
    (real-type vector-type point-type)
  (forall (p1 p2 p3)
    (implies
     (and
      (q11518-context-p real-type vector-type point-type)
      (q11518-point-member-p point-type p1)
      (q11518-point-member-p point-type p2)
      (q11518-point-member-p point-type p3))
     (iff
      (equal
       (q11518-distance-squared
        real-type vector-type point-type p1 p3)
       (q11518-add-r
        real-type
        (q11518-distance-squared
         real-type vector-type point-type p1 p2)
        (q11518-distance-squared
         real-type vector-type point-type p3 p2)))
      (q11518-right-angle-p
       real-type vector-type point-type p1 p2 p3)))))

(value-triple :itpeval-statement-checked)
:q
