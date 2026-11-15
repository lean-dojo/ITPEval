;; Statement-only formalization of Babel-formal corpus artifact linear_map:
;; for a linear map between arbitrary vector spaces over an arbitrary field
;; satisfying the source laws, its kernel and image are closed under addition
;; and scalar multiplication. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent the arbitrary scalar type, vector
;; types, their operations, and the linear map. Type closure and every source
;; algebraic law are explicit below; no carrier or function is finite-coded.

(defstub bf-lm-scalar-member-p (scalar-type value) t)
(defstub bf-lm-vector-member-p (vector-type value) t)

(defstub bf-lm-zero-r (scalar-type) t)
(defstub bf-lm-one-r (scalar-type) t)
(defstub bf-lm-add-r (scalar-type x y) t)
(defstub bf-lm-mul-r (scalar-type x y) t)
(defstub bf-lm-opp-r (scalar-type x) t)

(defstub bf-lm-zero-v (scalar-type vector-type) t)
(defstub bf-lm-add-v (scalar-type vector-type x y) t)
(defstub bf-lm-opp-v (scalar-type vector-type x) t)
(defstub bf-lm-smul (scalar-type vector-type scalar vector) t)

(defstub bf-lm-apply
  (scalar-type domain-type codomain-type map-tag vector)
  t)

(defun-sk bf-lm-field-laws-p (scalar-type)
  (forall (x y z)
    (and
     (implies
      (and
       (bf-lm-scalar-member-p scalar-type x)
       (bf-lm-scalar-member-p scalar-type y))
      (and
       (bf-lm-scalar-member-p
        scalar-type (bf-lm-add-r scalar-type x y))
       (bf-lm-scalar-member-p
        scalar-type (bf-lm-mul-r scalar-type x y))
       (equal
        (bf-lm-add-r scalar-type x y)
        (bf-lm-add-r scalar-type y x))
       (equal
        (bf-lm-mul-r scalar-type x y)
        (bf-lm-mul-r scalar-type y x))))
     (implies
      (bf-lm-scalar-member-p scalar-type x)
      (and
       (bf-lm-scalar-member-p
        scalar-type (bf-lm-opp-r scalar-type x))
       (equal
        (bf-lm-add-r scalar-type x (bf-lm-zero-r scalar-type))
        x)
       (equal
        (bf-lm-add-r
         scalar-type x (bf-lm-opp-r scalar-type x))
        (bf-lm-zero-r scalar-type))
       (equal
        (bf-lm-mul-r scalar-type x (bf-lm-one-r scalar-type))
        x)))
     (implies
      (and
       (bf-lm-scalar-member-p scalar-type x)
       (bf-lm-scalar-member-p scalar-type y)
       (bf-lm-scalar-member-p scalar-type z))
      (and
       (equal
        (bf-lm-add-r
         scalar-type (bf-lm-add-r scalar-type x y) z)
        (bf-lm-add-r
         scalar-type x (bf-lm-add-r scalar-type y z)))
       (equal
        (bf-lm-mul-r
         scalar-type (bf-lm-mul-r scalar-type x y) z)
        (bf-lm-mul-r
         scalar-type x (bf-lm-mul-r scalar-type y z)))
       (equal
        (bf-lm-mul-r
         scalar-type x (bf-lm-add-r scalar-type y z))
        (bf-lm-add-r
         scalar-type
         (bf-lm-mul-r scalar-type x y)
         (bf-lm-mul-r scalar-type x z))))))))

(defun bf-lm-field-p (scalar-type)
  (and
   (bf-lm-scalar-member-p
    scalar-type (bf-lm-zero-r scalar-type))
   (bf-lm-scalar-member-p
    scalar-type (bf-lm-one-r scalar-type))
   (bf-lm-field-laws-p scalar-type)))

(defun-sk bf-lm-vector-space-laws-p (scalar-type vector-type)
  (forall (a b u v w)
    (and
     (implies
      (and
       (bf-lm-vector-member-p vector-type u)
       (bf-lm-vector-member-p vector-type v))
      (and
       (bf-lm-vector-member-p
        vector-type
        (bf-lm-add-v scalar-type vector-type u v))
       (equal
        (bf-lm-add-v scalar-type vector-type u v)
        (bf-lm-add-v scalar-type vector-type v u))))
     (implies
      (bf-lm-vector-member-p vector-type u)
      (and
       (bf-lm-vector-member-p
        vector-type
        (bf-lm-opp-v scalar-type vector-type u))
       (equal
        (bf-lm-add-v
         scalar-type vector-type u
         (bf-lm-zero-v scalar-type vector-type))
        u)
       (equal
        (bf-lm-add-v
         scalar-type vector-type u
         (bf-lm-opp-v scalar-type vector-type u))
        (bf-lm-zero-v scalar-type vector-type))
       (equal
        (bf-lm-smul
         scalar-type vector-type
         (bf-lm-one-r scalar-type) u)
        u)))
     (implies
      (and
       (bf-lm-vector-member-p vector-type u)
       (bf-lm-vector-member-p vector-type v)
       (bf-lm-vector-member-p vector-type w))
      (equal
       (bf-lm-add-v
        scalar-type vector-type
        (bf-lm-add-v scalar-type vector-type u v)
        w)
       (bf-lm-add-v
        scalar-type vector-type
        u
        (bf-lm-add-v scalar-type vector-type v w))))
     (implies
      (and
       (bf-lm-scalar-member-p scalar-type a)
       (bf-lm-vector-member-p vector-type u))
      (bf-lm-vector-member-p
       vector-type
       (bf-lm-smul scalar-type vector-type a u)))
     (implies
      (bf-lm-scalar-member-p scalar-type a)
      (equal
       (bf-lm-smul
        scalar-type vector-type a
        (bf-lm-zero-v scalar-type vector-type))
       (bf-lm-zero-v scalar-type vector-type)))
     (implies
      (and
       (bf-lm-scalar-member-p scalar-type a)
       (bf-lm-vector-member-p vector-type u)
       (bf-lm-vector-member-p vector-type v))
      (equal
       (bf-lm-smul
        scalar-type vector-type a
        (bf-lm-add-v scalar-type vector-type u v))
       (bf-lm-add-v
        scalar-type vector-type
        (bf-lm-smul scalar-type vector-type a u)
        (bf-lm-smul scalar-type vector-type a v))))
     (implies
      (and
       (bf-lm-scalar-member-p scalar-type a)
       (bf-lm-scalar-member-p scalar-type b)
       (bf-lm-vector-member-p vector-type u))
      (and
       (equal
        (bf-lm-smul
         scalar-type vector-type
         (bf-lm-add-r scalar-type a b)
         u)
        (bf-lm-add-v
         scalar-type vector-type
         (bf-lm-smul scalar-type vector-type a u)
         (bf-lm-smul scalar-type vector-type b u)))
       (equal
        (bf-lm-smul
         scalar-type vector-type
         (bf-lm-mul-r scalar-type a b)
         u)
        (bf-lm-smul
         scalar-type vector-type a
         (bf-lm-smul scalar-type vector-type b u))))))))

(defun bf-lm-vector-space-p (scalar-type vector-type)
  (and
   (bf-lm-vector-member-p
    vector-type (bf-lm-zero-v scalar-type vector-type))
   (bf-lm-vector-space-laws-p scalar-type vector-type)))

(defun-sk bf-lm-linear-map-laws-p
    (scalar-type domain-type codomain-type map-tag)
  (forall (a u v)
    (and
     (implies
      (bf-lm-vector-member-p domain-type u)
      (bf-lm-vector-member-p
       codomain-type
       (bf-lm-apply
        scalar-type domain-type codomain-type map-tag u)))
     (implies
      (and
       (bf-lm-vector-member-p domain-type u)
       (bf-lm-vector-member-p domain-type v))
      (equal
       (bf-lm-apply
        scalar-type domain-type codomain-type map-tag
        (bf-lm-add-v scalar-type domain-type u v))
       (bf-lm-add-v
        scalar-type codomain-type
        (bf-lm-apply
         scalar-type domain-type codomain-type map-tag u)
        (bf-lm-apply
         scalar-type domain-type codomain-type map-tag v))))
     (implies
      (and
       (bf-lm-scalar-member-p scalar-type a)
       (bf-lm-vector-member-p domain-type u))
      (equal
       (bf-lm-apply
        scalar-type domain-type codomain-type map-tag
        (bf-lm-smul scalar-type domain-type a u))
       (bf-lm-smul
        scalar-type codomain-type a
        (bf-lm-apply
         scalar-type domain-type codomain-type map-tag u)))))))

(defun bf-lm-context-p
    (scalar-type domain-type codomain-type map-tag)
  (and
   (bf-lm-field-p scalar-type)
   (bf-lm-vector-space-p scalar-type domain-type)
   (bf-lm-vector-space-p scalar-type codomain-type)
   (bf-lm-linear-map-laws-p
    scalar-type domain-type codomain-type map-tag)))

(defun bf-lm-kernel-p
    (scalar-type domain-type codomain-type map-tag x)
  (equal
   (bf-lm-apply
    scalar-type domain-type codomain-type map-tag x)
   (bf-lm-zero-v scalar-type codomain-type)))

(defun-sk bf-lm-image-p
    (scalar-type domain-type codomain-type map-tag y)
  (exists (x)
    (and
     (bf-lm-vector-member-p domain-type x)
     (equal
      (bf-lm-apply
       scalar-type domain-type codomain-type map-tag x)
      y))))

(defun-sk bf-lm-kernel-add-statement ()
  (forall
    (scalar-type domain-type codomain-type map-tag x y)
    (implies
     (and
      (bf-lm-context-p
       scalar-type domain-type codomain-type map-tag)
      (bf-lm-vector-member-p domain-type x)
      (bf-lm-vector-member-p domain-type y)
      (bf-lm-kernel-p
       scalar-type domain-type codomain-type map-tag x)
      (bf-lm-kernel-p
       scalar-type domain-type codomain-type map-tag y))
     (bf-lm-kernel-p
      scalar-type domain-type codomain-type map-tag
      (bf-lm-add-v scalar-type domain-type x y)))))

(defun-sk bf-lm-kernel-smul-statement ()
  (forall
    (scalar-type domain-type codomain-type map-tag a x)
    (implies
     (and
      (bf-lm-context-p
       scalar-type domain-type codomain-type map-tag)
      (bf-lm-scalar-member-p scalar-type a)
      (bf-lm-vector-member-p domain-type x)
      (bf-lm-kernel-p
       scalar-type domain-type codomain-type map-tag x))
     (bf-lm-kernel-p
      scalar-type domain-type codomain-type map-tag
      (bf-lm-smul scalar-type domain-type a x)))))

(defun-sk bf-lm-image-add-statement ()
  (forall
    (scalar-type domain-type codomain-type map-tag y z)
    (implies
     (and
      (bf-lm-context-p
       scalar-type domain-type codomain-type map-tag)
      (bf-lm-vector-member-p codomain-type y)
      (bf-lm-vector-member-p codomain-type z)
      (bf-lm-image-p
       scalar-type domain-type codomain-type map-tag y)
      (bf-lm-image-p
       scalar-type domain-type codomain-type map-tag z))
     (bf-lm-image-p
      scalar-type domain-type codomain-type map-tag
      (bf-lm-add-v scalar-type codomain-type y z)))))

(defun-sk bf-lm-image-smul-statement ()
  (forall
    (scalar-type domain-type codomain-type map-tag a y)
    (implies
     (and
      (bf-lm-context-p
       scalar-type domain-type codomain-type map-tag)
      (bf-lm-scalar-member-p scalar-type a)
      (bf-lm-vector-member-p codomain-type y)
      (bf-lm-image-p
       scalar-type domain-type codomain-type map-tag y))
     (bf-lm-image-p
      scalar-type domain-type codomain-type map-tag
      (bf-lm-smul scalar-type codomain-type a y)))))

(defun babel-formal-linear-map-statement ()
  (and
   (bf-lm-kernel-add-statement)
   (bf-lm-kernel-smul-statement)
   (bf-lm-image-add-statement)
   (bf-lm-image-smul-statement)))

(value-triple :itpeval-statement-checked)
:q
