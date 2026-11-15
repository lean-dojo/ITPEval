;; Statement-only formalization of Babel-formal artifact inner_product: six
;; negation, expansion, Pythagorean, and parallelogram identities for a
;; symmetric bilinear inner product over arbitrary scalar and vector carriers
;; satisfying the source's algebraic laws. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent the two arbitrary source types and
;; every operation carried by Field, VSpace, and Inner. All typing and
;; algebraic laws are explicit below; no carrier or function is finite-coded.

(defstub bf-ip-scalar-member-p (scalar-type x) t)
(defstub bf-ip-vector-member-p (vector-type x) t)

(defstub bf-ip-zero-r (scalar-type) t)
(defstub bf-ip-one-r (scalar-type) t)
(defstub bf-ip-add-r (scalar-type x y) t)
(defstub bf-ip-mul-r (scalar-type x y) t)
(defstub bf-ip-opp-r (scalar-type x) t)

(defstub bf-ip-zero-v (scalar-type vector-type) t)
(defstub bf-ip-add-v (scalar-type vector-type x y) t)
(defstub bf-ip-opp-v (scalar-type vector-type x) t)
(defstub bf-ip-smul (scalar-type vector-type a x) t)
(defstub bf-ip-inner (scalar-type vector-type x y) t)

(defun-sk bf-ip-field-laws-p (scalar-type)
  (forall (x y z)
    (implies
     (and
      (bf-ip-scalar-member-p scalar-type x)
      (bf-ip-scalar-member-p scalar-type y)
      (bf-ip-scalar-member-p scalar-type z))
     (let ((zero (bf-ip-zero-r scalar-type))
           (one (bf-ip-one-r scalar-type)))
       (and
        ;; Closure is the ACL2 rendering of the source operations' result
        ;; types.
        (bf-ip-scalar-member-p
         scalar-type (bf-ip-add-r scalar-type x y))
        (bf-ip-scalar-member-p
         scalar-type (bf-ip-mul-r scalar-type x y))
        (bf-ip-scalar-member-p
         scalar-type (bf-ip-opp-r scalar-type x))

        (equal (bf-ip-add-r scalar-type x y)
               (bf-ip-add-r scalar-type y x))
        (equal
         (bf-ip-add-r
          scalar-type (bf-ip-add-r scalar-type x y) z)
         (bf-ip-add-r
          scalar-type x (bf-ip-add-r scalar-type y z)))
        (equal (bf-ip-add-r scalar-type x zero) x)
        (equal (bf-ip-add-r scalar-type zero x) x)
        (equal
         (bf-ip-add-r
          scalar-type x (bf-ip-opp-r scalar-type x))
         zero)

        (equal (bf-ip-mul-r scalar-type x y)
               (bf-ip-mul-r scalar-type y x))
        (equal
         (bf-ip-mul-r
          scalar-type (bf-ip-mul-r scalar-type x y) z)
         (bf-ip-mul-r
          scalar-type x (bf-ip-mul-r scalar-type y z)))
        (equal (bf-ip-mul-r scalar-type x one) x)
        (equal
         (bf-ip-mul-r
          scalar-type x (bf-ip-add-r scalar-type y z))
         (bf-ip-add-r
          scalar-type
          (bf-ip-mul-r scalar-type x y)
          (bf-ip-mul-r scalar-type x z)))

        (equal
         (bf-ip-opp-r
          scalar-type (bf-ip-add-r scalar-type x y))
         (bf-ip-add-r
          scalar-type
          (bf-ip-opp-r scalar-type x)
          (bf-ip-opp-r scalar-type y)))
        (equal
         (bf-ip-mul-r
          scalar-type (bf-ip-opp-r scalar-type one) x)
         (bf-ip-opp-r scalar-type x))
        (equal
         (bf-ip-opp-r
          scalar-type (bf-ip-opp-r scalar-type x))
         x))))))

(defun bf-ip-field-p (scalar-type)
  (and
   (bf-ip-scalar-member-p
    scalar-type (bf-ip-zero-r scalar-type))
   (bf-ip-scalar-member-p
    scalar-type (bf-ip-one-r scalar-type))
   (bf-ip-field-laws-p scalar-type)))

(defun-sk bf-ip-vector-space-laws-p (scalar-type vector-type)
  (forall (a b u v w)
    (implies
     (and
      (bf-ip-scalar-member-p scalar-type a)
      (bf-ip-scalar-member-p scalar-type b)
      (bf-ip-vector-member-p vector-type u)
      (bf-ip-vector-member-p vector-type v)
      (bf-ip-vector-member-p vector-type w))
     (let ((one-r (bf-ip-one-r scalar-type))
           (zero-v (bf-ip-zero-v scalar-type vector-type)))
       (and
        (bf-ip-vector-member-p
         vector-type
         (bf-ip-add-v scalar-type vector-type u v))
        (bf-ip-vector-member-p
         vector-type
         (bf-ip-opp-v scalar-type vector-type u))
        (bf-ip-vector-member-p
         vector-type
         (bf-ip-smul scalar-type vector-type a u))

        (equal
         (bf-ip-add-v scalar-type vector-type u v)
         (bf-ip-add-v scalar-type vector-type v u))
        (equal
         (bf-ip-add-v
          scalar-type vector-type
          (bf-ip-add-v scalar-type vector-type u v)
          w)
         (bf-ip-add-v
          scalar-type vector-type
          u
          (bf-ip-add-v scalar-type vector-type v w)))
        (equal
         (bf-ip-add-v scalar-type vector-type u zero-v)
         u)
        (equal
         (bf-ip-add-v
          scalar-type vector-type
          u
          (bf-ip-opp-v scalar-type vector-type u))
         zero-v)

        (equal
         (bf-ip-smul
          scalar-type vector-type
          a
          (bf-ip-add-v scalar-type vector-type u v))
         (bf-ip-add-v
          scalar-type vector-type
          (bf-ip-smul scalar-type vector-type a u)
          (bf-ip-smul scalar-type vector-type a v)))
        (equal
         (bf-ip-smul
          scalar-type vector-type
          (bf-ip-add-r scalar-type a b)
          u)
         (bf-ip-add-v
          scalar-type vector-type
          (bf-ip-smul scalar-type vector-type a u)
          (bf-ip-smul scalar-type vector-type b u)))
        (equal
         (bf-ip-smul
          scalar-type vector-type
          (bf-ip-mul-r scalar-type a b)
          u)
         (bf-ip-smul
          scalar-type vector-type
          a
          (bf-ip-smul scalar-type vector-type b u)))
        (equal
         (bf-ip-smul scalar-type vector-type one-r u)
         u)
        (equal
         (bf-ip-smul scalar-type vector-type a zero-v)
         zero-v)
        (equal
         (bf-ip-opp-v scalar-type vector-type u)
         (bf-ip-smul
          scalar-type vector-type
          (bf-ip-opp-r scalar-type one-r)
          u)))))))

(defun bf-ip-vector-space-p (scalar-type vector-type)
  (and
   (bf-ip-vector-member-p
    vector-type (bf-ip-zero-v scalar-type vector-type))
   (bf-ip-vector-space-laws-p scalar-type vector-type)))

(defun-sk bf-ip-inner-laws-p (scalar-type vector-type)
  (forall (a u v w)
    (implies
     (and
      (bf-ip-scalar-member-p scalar-type a)
      (bf-ip-vector-member-p vector-type u)
      (bf-ip-vector-member-p vector-type v)
      (bf-ip-vector-member-p vector-type w))
     (and
      (bf-ip-scalar-member-p
       scalar-type
       (bf-ip-inner scalar-type vector-type u v))
      (equal
       (bf-ip-inner
        scalar-type vector-type
        (bf-ip-add-v scalar-type vector-type u v)
        w)
       (bf-ip-add-r
        scalar-type
        (bf-ip-inner scalar-type vector-type u w)
        (bf-ip-inner scalar-type vector-type v w)))
      (equal
       (bf-ip-inner
        scalar-type vector-type
        (bf-ip-smul scalar-type vector-type a u)
        v)
       (bf-ip-mul-r
        scalar-type
        a
        (bf-ip-inner scalar-type vector-type u v)))
      (equal
       (bf-ip-inner
        scalar-type vector-type
        u
        (bf-ip-add-v scalar-type vector-type v w))
       (bf-ip-add-r
        scalar-type
        (bf-ip-inner scalar-type vector-type u v)
        (bf-ip-inner scalar-type vector-type u w)))
      (equal
       (bf-ip-inner
        scalar-type vector-type
        u
        (bf-ip-smul scalar-type vector-type a v))
       (bf-ip-mul-r
        scalar-type
        a
        (bf-ip-inner scalar-type vector-type u v)))
      (equal
       (bf-ip-inner scalar-type vector-type u v)
       (bf-ip-inner scalar-type vector-type v u))))))

(defun bf-ip-context-p (scalar-type vector-type)
  (and
   (bf-ip-field-p scalar-type)
   (bf-ip-vector-space-p scalar-type vector-type)
   (bf-ip-inner-laws-p scalar-type vector-type)))

(defun bf-ip-sub-v (scalar-type vector-type u v)
  (bf-ip-add-v
   scalar-type vector-type
   u
   (bf-ip-opp-v scalar-type vector-type v)))

(defun bf-ip-sum-expansion (scalar-type vector-type u v)
  (bf-ip-add-r
   scalar-type
   (bf-ip-add-r
    scalar-type
    (bf-ip-inner scalar-type vector-type u u)
    (bf-ip-inner scalar-type vector-type v u))
   (bf-ip-add-r
    scalar-type
    (bf-ip-inner scalar-type vector-type u v)
    (bf-ip-inner scalar-type vector-type v v))))

(defun bf-ip-difference-expansion
    (scalar-type vector-type u v)
  (bf-ip-add-r
   scalar-type
   (bf-ip-add-r
    scalar-type
    (bf-ip-inner scalar-type vector-type u u)
    (bf-ip-opp-r
     scalar-type
     (bf-ip-inner scalar-type vector-type v u)))
   (bf-ip-add-r
    scalar-type
    (bf-ip-opp-r
     scalar-type
     (bf-ip-inner scalar-type vector-type u v))
    (bf-ip-inner scalar-type vector-type v v))))

(defun bf-ip-typed-pair-p (scalar-type vector-type u v)
  (and
   (bf-ip-context-p scalar-type vector-type)
   (bf-ip-vector-member-p vector-type u)
   (bf-ip-vector-member-p vector-type v)))

(defun-sk bf-ip-neg-left-statement (scalar-type vector-type)
  (forall (u v)
    (implies
     (bf-ip-typed-pair-p scalar-type vector-type u v)
     (equal
      (bf-ip-inner
       scalar-type vector-type
       (bf-ip-opp-v scalar-type vector-type u)
       v)
      (bf-ip-opp-r
       scalar-type
       (bf-ip-inner scalar-type vector-type u v))))))

(defun-sk bf-ip-neg-right-statement (scalar-type vector-type)
  (forall (u v)
    (implies
     (bf-ip-typed-pair-p scalar-type vector-type u v)
     (equal
      (bf-ip-inner
       scalar-type vector-type
       u
       (bf-ip-opp-v scalar-type vector-type v))
      (bf-ip-opp-r
       scalar-type
       (bf-ip-inner scalar-type vector-type u v))))))

(defun-sk bf-ip-add-add-statement (scalar-type vector-type)
  (forall (u v)
    (implies
     (bf-ip-typed-pair-p scalar-type vector-type u v)
     (equal
      (bf-ip-inner
       scalar-type vector-type
       (bf-ip-add-v scalar-type vector-type u v)
       (bf-ip-add-v scalar-type vector-type u v))
      (bf-ip-sum-expansion scalar-type vector-type u v)))))

(defun-sk bf-ip-sub-sub-statement (scalar-type vector-type)
  (forall (u v)
    (implies
     (bf-ip-typed-pair-p scalar-type vector-type u v)
     (equal
      (bf-ip-inner
       scalar-type vector-type
       (bf-ip-sub-v scalar-type vector-type u v)
       (bf-ip-sub-v scalar-type vector-type u v))
      (bf-ip-difference-expansion
       scalar-type vector-type u v)))))

(defun-sk bf-ip-pythagoras-statement (scalar-type vector-type)
  (forall (u v)
    (implies
     (and
      (bf-ip-typed-pair-p scalar-type vector-type u v)
      (equal
       (bf-ip-inner scalar-type vector-type u v)
       (bf-ip-zero-r scalar-type)))
     (equal
      (bf-ip-inner
       scalar-type vector-type
       (bf-ip-add-v scalar-type vector-type u v)
       (bf-ip-add-v scalar-type vector-type u v))
      (bf-ip-add-r
       scalar-type
       (bf-ip-inner scalar-type vector-type u u)
       (bf-ip-inner scalar-type vector-type v v))))))

(defun-sk bf-ip-parallelogram-statement (scalar-type vector-type)
  (forall (u v)
    (implies
     (bf-ip-typed-pair-p scalar-type vector-type u v)
     (equal
      (bf-ip-add-r
       scalar-type
       (bf-ip-inner
        scalar-type vector-type
        (bf-ip-add-v scalar-type vector-type u v)
        (bf-ip-add-v scalar-type vector-type u v))
       (bf-ip-inner
        scalar-type vector-type
        (bf-ip-sub-v scalar-type vector-type u v)
        (bf-ip-sub-v scalar-type vector-type u v)))
      (bf-ip-add-r
       scalar-type
       (bf-ip-sum-expansion scalar-type vector-type u v)
       (bf-ip-difference-expansion
        scalar-type vector-type u v))))))

(defun babel-formal-inner-product-statement
    (scalar-type vector-type)
  (and
   (bf-ip-neg-left-statement scalar-type vector-type)
   (bf-ip-neg-right-statement scalar-type vector-type)
   (bf-ip-add-add-statement scalar-type vector-type)
   (bf-ip-sub-sub-statement scalar-type vector-type)
   (bf-ip-pythagoras-statement scalar-type vector-type)
   (bf-ip-parallelogram-statement scalar-type vector-type)))

(value-triple :itpeval-statement-checked)
:q
