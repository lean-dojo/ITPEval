;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__004, "Pythagorean Theorem": in an arbitrary real
;; inner-product space, orthogonal vectors have additive squared norms. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no built-in abstract real inner-product-space interface. The
;; conservative function symbols below represent arbitrary scalar and vector
;; carriers. Every algebraic and order law needed to interpret them as a real
;; inner-product space remains an explicit hypothesis of the statement.

(defstub ht004-scalar-member-p (scalar-type x) t)
(defstub ht004-vector-member-p (vector-type x) t)

(defstub ht004-zero-r (scalar-type) t)
(defstub ht004-one-r (scalar-type) t)
(defstub ht004-add-r (scalar-type x y) t)
(defstub ht004-mul-r (scalar-type x y) t)
(defstub ht004-opp-r (scalar-type x) t)
(defstub ht004-inv-r (scalar-type x) t)
(defstub ht004-le-r (scalar-type x y) t)

(defstub ht004-zero-v (scalar-type vector-type) t)
(defstub ht004-add-v (scalar-type vector-type x y) t)
(defstub ht004-opp-v (scalar-type vector-type x) t)
(defstub ht004-smul (scalar-type vector-type a x) t)
(defstub ht004-inner (scalar-type vector-type x y) t)

(defun-sk ht004-ordered-field-laws-p (scalar-type)
  (forall (x y z)
    (implies
     (and
      (ht004-scalar-member-p scalar-type x)
      (ht004-scalar-member-p scalar-type y)
      (ht004-scalar-member-p scalar-type z))
     (let ((zero (ht004-zero-r scalar-type))
           (one (ht004-one-r scalar-type)))
       (and
        (ht004-scalar-member-p
         scalar-type (ht004-add-r scalar-type x y))
        (ht004-scalar-member-p
         scalar-type (ht004-mul-r scalar-type x y))
        (ht004-scalar-member-p
         scalar-type (ht004-opp-r scalar-type x))
        (ht004-scalar-member-p
         scalar-type (ht004-inv-r scalar-type x))

        (equal
         (ht004-add-r scalar-type x y)
         (ht004-add-r scalar-type y x))
        (equal
         (ht004-add-r
          scalar-type (ht004-add-r scalar-type x y) z)
         (ht004-add-r
          scalar-type x (ht004-add-r scalar-type y z)))
        (equal (ht004-add-r scalar-type x zero) x)
        (equal
         (ht004-add-r
          scalar-type x (ht004-opp-r scalar-type x))
         zero)

        (equal
         (ht004-mul-r scalar-type x y)
         (ht004-mul-r scalar-type y x))
        (equal
         (ht004-mul-r
          scalar-type (ht004-mul-r scalar-type x y) z)
         (ht004-mul-r
          scalar-type x (ht004-mul-r scalar-type y z)))
        (equal (ht004-mul-r scalar-type x one) x)
        (equal (ht004-mul-r scalar-type x zero) zero)
        (equal
         (ht004-mul-r
          scalar-type x (ht004-add-r scalar-type y z))
         (ht004-add-r
          scalar-type
          (ht004-mul-r scalar-type x y)
          (ht004-mul-r scalar-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (ht004-mul-r
           scalar-type x (ht004-inv-r scalar-type x))
          one))

        (ht004-le-r scalar-type x x)
        (implies
         (and
          (ht004-le-r scalar-type x y)
          (ht004-le-r scalar-type y x))
         (equal x y))
        (implies
         (and
          (ht004-le-r scalar-type x y)
          (ht004-le-r scalar-type y z))
         (ht004-le-r scalar-type x z))
        (or
         (ht004-le-r scalar-type x y)
         (ht004-le-r scalar-type y x))
        (implies
         (ht004-le-r scalar-type x y)
         (ht004-le-r
          scalar-type
          (ht004-add-r scalar-type x z)
          (ht004-add-r scalar-type y z)))
        (implies
         (and
          (ht004-le-r scalar-type zero x)
          (ht004-le-r scalar-type zero y))
         (ht004-le-r
          scalar-type zero (ht004-mul-r scalar-type x y))))))))

(defun ht004-ordered-field-p (scalar-type)
  (and
   (ht004-scalar-member-p
    scalar-type (ht004-zero-r scalar-type))
   (ht004-scalar-member-p
    scalar-type (ht004-one-r scalar-type))
   (not
    (equal
     (ht004-zero-r scalar-type)
     (ht004-one-r scalar-type)))
   (ht004-ordered-field-laws-p scalar-type)))

(defun-sk ht004-vector-space-laws-p (scalar-type vector-type)
  (forall (a b u v w)
    (implies
     (and
      (ht004-scalar-member-p scalar-type a)
      (ht004-scalar-member-p scalar-type b)
      (ht004-vector-member-p vector-type u)
      (ht004-vector-member-p vector-type v)
      (ht004-vector-member-p vector-type w))
     (let ((one (ht004-one-r scalar-type))
           (zero-v (ht004-zero-v scalar-type vector-type)))
       (and
        (ht004-vector-member-p
         vector-type
         (ht004-add-v scalar-type vector-type u v))
        (ht004-vector-member-p
         vector-type
         (ht004-opp-v scalar-type vector-type u))
        (ht004-vector-member-p
         vector-type
         (ht004-smul scalar-type vector-type a u))

        (equal
         (ht004-add-v scalar-type vector-type u v)
         (ht004-add-v scalar-type vector-type v u))
        (equal
         (ht004-add-v
          scalar-type vector-type
          (ht004-add-v scalar-type vector-type u v)
          w)
         (ht004-add-v
          scalar-type vector-type
          u
          (ht004-add-v scalar-type vector-type v w)))
        (equal
         (ht004-add-v scalar-type vector-type u zero-v)
         u)
        (equal
         (ht004-add-v
          scalar-type vector-type
          u
          (ht004-opp-v scalar-type vector-type u))
         zero-v)

        (equal
         (ht004-smul
          scalar-type vector-type
          a
          (ht004-add-v scalar-type vector-type u v))
         (ht004-add-v
          scalar-type vector-type
          (ht004-smul scalar-type vector-type a u)
          (ht004-smul scalar-type vector-type a v)))
        (equal
         (ht004-smul
          scalar-type vector-type
          (ht004-add-r scalar-type a b)
          u)
         (ht004-add-v
          scalar-type vector-type
          (ht004-smul scalar-type vector-type a u)
          (ht004-smul scalar-type vector-type b u)))
        (equal
         (ht004-smul
          scalar-type vector-type
          (ht004-mul-r scalar-type a b)
          u)
         (ht004-smul
          scalar-type vector-type
          a
          (ht004-smul scalar-type vector-type b u)))
        (equal
         (ht004-smul scalar-type vector-type one u)
         u))))))

(defun ht004-vector-space-p (scalar-type vector-type)
  (and
   (ht004-vector-member-p
    vector-type (ht004-zero-v scalar-type vector-type))
   (ht004-vector-space-laws-p scalar-type vector-type)))

(defun-sk ht004-inner-product-laws-p (scalar-type vector-type)
  (forall (a u v w)
    (implies
     (and
      (ht004-scalar-member-p scalar-type a)
      (ht004-vector-member-p vector-type u)
      (ht004-vector-member-p vector-type v)
      (ht004-vector-member-p vector-type w))
     (let ((zero-r (ht004-zero-r scalar-type))
           (zero-v (ht004-zero-v scalar-type vector-type)))
       (and
        (ht004-scalar-member-p
         scalar-type
         (ht004-inner scalar-type vector-type u v))
        (equal
         (ht004-inner scalar-type vector-type u v)
         (ht004-inner scalar-type vector-type v u))
        (equal
         (ht004-inner
          scalar-type vector-type
          (ht004-add-v scalar-type vector-type u v)
          w)
         (ht004-add-r
          scalar-type
          (ht004-inner scalar-type vector-type u w)
          (ht004-inner scalar-type vector-type v w)))
        (equal
         (ht004-inner
          scalar-type vector-type
          (ht004-smul scalar-type vector-type a u)
          v)
         (ht004-mul-r
          scalar-type a
          (ht004-inner scalar-type vector-type u v)))
        (ht004-le-r
         scalar-type zero-r
         (ht004-inner scalar-type vector-type u u))
        (equal
         (equal
          (ht004-inner scalar-type vector-type u u)
          zero-r)
         (equal u zero-v)))))))

(defun ht004-real-inner-product-space-p (scalar-type vector-type)
  (and
   (ht004-ordered-field-p scalar-type)
   (ht004-vector-space-p scalar-type vector-type)
   (ht004-inner-product-laws-p scalar-type vector-type)))

(defun ht004-squared-norm
    (scalar-type vector-type vector)
  (ht004-inner scalar-type vector-type vector vector))

(defun-sk hundred-theorems-004-pythagorean-theorem-statement
    (scalar-type vector-type)
  (forall (u v)
    (implies
     (and
      (ht004-real-inner-product-space-p scalar-type vector-type)
      (ht004-vector-member-p vector-type u)
      (ht004-vector-member-p vector-type v)
      (equal
       (ht004-inner scalar-type vector-type u v)
       (ht004-zero-r scalar-type)))
     (equal
      (ht004-squared-norm
       scalar-type
       vector-type
       (ht004-add-v scalar-type vector-type u v))
      (ht004-add-r
       scalar-type
       (ht004-squared-norm scalar-type vector-type u)
       (ht004-squared-norm scalar-type vector-type v))))))

(value-triple :itpeval-statement-checked)
:q
