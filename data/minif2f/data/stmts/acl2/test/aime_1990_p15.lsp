;; Statement-only formalization of miniF2F artifact aime_1990_p15:
;; for real a, b, x, and y, weighted power sums at exponents 1 through 4
;; equal to 3, 7, 16, and 42 imply that the fifth weighted sum is 20.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no built-in first-class real field. The arbitrary carrier below
;; is constrained only through explicit ordered-field laws in the theorem
;; antecedent, so the source variables still range over the full real domain.

(defstub aime-1990-p15-real-p (real-type value) t)
(defstub aime-1990-p15-zero (real-type) t)
(defstub aime-1990-p15-one (real-type) t)
(defstub aime-1990-p15-add (real-type left right) t)
(defstub aime-1990-p15-mul (real-type left right) t)
(defstub aime-1990-p15-neg (real-type value) t)
(defstub aime-1990-p15-inv (real-type value) t)
(defstub aime-1990-p15-le (real-type left right) t)
(defstub aime-1990-p15-of-rational (real-type rational) t)

(defun-sk aime-1990-p15-closure-laws-p (real-type)
  (forall (u v)
    (and
     (aime-1990-p15-real-p
      real-type (aime-1990-p15-zero real-type))
     (aime-1990-p15-real-p
      real-type (aime-1990-p15-one real-type))
     (implies
      (aime-1990-p15-real-p real-type u)
      (and
       (aime-1990-p15-real-p
        real-type (aime-1990-p15-neg real-type u))
       (aime-1990-p15-real-p
        real-type (aime-1990-p15-inv real-type u))))
     (implies
      (and
       (aime-1990-p15-real-p real-type u)
       (aime-1990-p15-real-p real-type v))
      (and
       (aime-1990-p15-real-p
        real-type (aime-1990-p15-add real-type u v))
       (aime-1990-p15-real-p
        real-type (aime-1990-p15-mul real-type u v)))))))

(defun-sk aime-1990-p15-field-laws-p (real-type)
  (forall (u v w)
    (implies
     (and
      (aime-1990-p15-real-p real-type u)
      (aime-1990-p15-real-p real-type v)
      (aime-1990-p15-real-p real-type w))
     (let ((zero (aime-1990-p15-zero real-type))
           (one (aime-1990-p15-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (aime-1990-p15-add real-type u v)
         (aime-1990-p15-add real-type v u))
        (equal
         (aime-1990-p15-add
          real-type
          (aime-1990-p15-add real-type u v)
          w)
         (aime-1990-p15-add
          real-type
          u
          (aime-1990-p15-add real-type v w)))
        (equal (aime-1990-p15-add real-type u zero) u)
        (equal
         (aime-1990-p15-add
          real-type u (aime-1990-p15-neg real-type u))
         zero)
        (equal
         (aime-1990-p15-mul real-type u v)
         (aime-1990-p15-mul real-type v u))
        (equal
         (aime-1990-p15-mul
          real-type
          (aime-1990-p15-mul real-type u v)
          w)
         (aime-1990-p15-mul
          real-type
          u
          (aime-1990-p15-mul real-type v w)))
        (equal (aime-1990-p15-mul real-type u one) u)
        (equal
         (aime-1990-p15-mul
          real-type
          u
          (aime-1990-p15-add real-type v w))
         (aime-1990-p15-add
          real-type
          (aime-1990-p15-mul real-type u v)
          (aime-1990-p15-mul real-type u w)))
        (implies
         (not (equal u zero))
         (equal
          (aime-1990-p15-mul
           real-type u (aime-1990-p15-inv real-type u))
          one)))))))

(defun-sk aime-1990-p15-order-laws-p (real-type)
  (forall (u v w)
    (implies
     (and
      (aime-1990-p15-real-p real-type u)
      (aime-1990-p15-real-p real-type v)
      (aime-1990-p15-real-p real-type w))
     (let ((zero (aime-1990-p15-zero real-type)))
       (and
        (aime-1990-p15-le real-type u u)
        (implies
         (and
          (aime-1990-p15-le real-type u v)
          (aime-1990-p15-le real-type v u))
         (equal u v))
        (implies
         (and
          (aime-1990-p15-le real-type u v)
          (aime-1990-p15-le real-type v w))
         (aime-1990-p15-le real-type u w))
        (or
         (aime-1990-p15-le real-type u v)
         (aime-1990-p15-le real-type v u))
        (implies
         (aime-1990-p15-le real-type u v)
         (aime-1990-p15-le
          real-type
          (aime-1990-p15-add real-type u w)
          (aime-1990-p15-add real-type v w)))
        (implies
         (and
          (aime-1990-p15-le real-type zero u)
          (aime-1990-p15-le real-type zero v))
         (aime-1990-p15-le
          real-type
          zero
          (aime-1990-p15-mul real-type u v))))))))

(defun-sk aime-1990-p15-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (aime-1990-p15-real-p
       real-type (aime-1990-p15-of-rational real-type p))
      (equal
       (aime-1990-p15-of-rational real-type 0)
       (aime-1990-p15-zero real-type))
      (equal
       (aime-1990-p15-of-rational real-type 1)
       (aime-1990-p15-one real-type))
      (equal
       (aime-1990-p15-of-rational real-type (+ p q))
       (aime-1990-p15-add
        real-type
        (aime-1990-p15-of-rational real-type p)
        (aime-1990-p15-of-rational real-type q)))
      (equal
       (aime-1990-p15-of-rational real-type (* p q))
       (aime-1990-p15-mul
        real-type
        (aime-1990-p15-of-rational real-type p)
        (aime-1990-p15-of-rational real-type q)))
      (equal
       (aime-1990-p15-of-rational real-type (- p))
       (aime-1990-p15-neg
        real-type
        (aime-1990-p15-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (aime-1990-p15-of-rational real-type p)
        (aime-1990-p15-of-rational real-type q)))
      (iff
       (<= p q)
       (aime-1990-p15-le
        real-type
        (aime-1990-p15-of-rational real-type p)
        (aime-1990-p15-of-rational real-type q)))))))

(defun aime-1990-p15-real-structure-p (real-type)
  (and
   (aime-1990-p15-closure-laws-p real-type)
   (aime-1990-p15-field-laws-p real-type)
   (aime-1990-p15-order-laws-p real-type)
   (aime-1990-p15-rational-laws-p real-type)))

(defun aime-1990-p15-pow (real-type value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime-1990-p15-one real-type)
    (aime-1990-p15-mul
     real-type
     value
     (aime-1990-p15-pow real-type value (1- exponent)))))

(defun aime-1990-p15-weighted-power-sum
    (real-type a b x y exponent)
  (aime-1990-p15-add
   real-type
   (aime-1990-p15-mul
    real-type
    a
    (aime-1990-p15-pow real-type x exponent))
   (aime-1990-p15-mul
    real-type
    b
    (aime-1990-p15-pow real-type y exponent))))

(defun-sk aime-1990-p15-statement ()
  (forall (real-type a b x y)
    (implies
     (and
      (aime-1990-p15-real-structure-p real-type)
      (aime-1990-p15-real-p real-type a)
      (aime-1990-p15-real-p real-type b)
      (aime-1990-p15-real-p real-type x)
      (aime-1990-p15-real-p real-type y)
      (equal
       (aime-1990-p15-weighted-power-sum
        real-type a b x y 1)
       (aime-1990-p15-of-rational real-type 3))
      (equal
       (aime-1990-p15-weighted-power-sum
        real-type a b x y 2)
       (aime-1990-p15-of-rational real-type 7))
      (equal
       (aime-1990-p15-weighted-power-sum
        real-type a b x y 3)
       (aime-1990-p15-of-rational real-type 16))
      (equal
       (aime-1990-p15-weighted-power-sum
        real-type a b x y 4)
       (aime-1990-p15-of-rational real-type 42)))
     (equal
      (aime-1990-p15-weighted-power-sum
       real-type a b x y 5)
      (aime-1990-p15-of-rational real-type 20)))))

(value-triple :itpeval-statement-checked)
:q
