;; Statement-only formalization of miniF2F artifact amc12a_2020_p13:
;; the stated nested positive-real reciprocal-power identity implies b = 3.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no full real-power operation. The arbitrary carrier,
;; ordered-field operations, rational embedding, and generic real-power laws
;; below are explicit premises. The source base n and every nested reciprocal
;; power remain literal; no theorem-specific exponent normalization is used.

(defstub amc20p13-real-p (real-type value) t)
(defstub amc20p13-zero (real-type) t)
(defstub amc20p13-one (real-type) t)
(defstub amc20p13-add (real-type left right) t)
(defstub amc20p13-mul (real-type left right) t)
(defstub amc20p13-neg (real-type value) t)
(defstub amc20p13-inv (real-type value) t)
(defstub amc20p13-le (real-type left right) t)
(defstub amc20p13-of-rational (real-type rational) t)
(defstub amc20p13-rpow (real-type base exponent) t)

(defun amc20p13-div (real-type x y)
  (amc20p13-mul real-type x (amc20p13-inv real-type y)))

(defun amc20p13-lt (real-type x y)
  (and
   (amc20p13-le real-type x y)
   (not (equal x y))))

(defun amc20p13-positive-p (real-type x)
  (and
   (amc20p13-real-p real-type x)
   (amc20p13-lt real-type (amc20p13-zero real-type) x)))

(defun amc20p13-natural-power (real-type x exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amc20p13-one real-type)
    (amc20p13-mul
     real-type
     x
     (amc20p13-natural-power real-type x (- exponent 1)))))

(defun amc20p13-unit-fraction (real-type denominator)
  (amc20p13-div
   real-type
   (amc20p13-one real-type)
   (amc20p13-of-rational real-type denominator)))

(defun-sk amc20p13-closure-laws-p (real-type)
  (forall (x y)
    (and
     (amc20p13-real-p real-type (amc20p13-zero real-type))
     (amc20p13-real-p real-type (amc20p13-one real-type))
     (implies
      (amc20p13-real-p real-type x)
      (and
       (amc20p13-real-p real-type (amc20p13-neg real-type x))
       (amc20p13-real-p real-type (amc20p13-inv real-type x))))
     (implies
      (and
       (amc20p13-real-p real-type x)
       (amc20p13-real-p real-type y))
      (and
       (amc20p13-real-p real-type (amc20p13-add real-type x y))
       (amc20p13-real-p real-type (amc20p13-mul real-type x y)))))))

(defun-sk amc20p13-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc20p13-real-p real-type x)
      (amc20p13-real-p real-type y)
      (amc20p13-real-p real-type z))
     (let ((zero (amc20p13-zero real-type))
           (one (amc20p13-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (amc20p13-add real-type x y)
         (amc20p13-add real-type y x))
        (equal
         (amc20p13-add real-type (amc20p13-add real-type x y) z)
         (amc20p13-add real-type x (amc20p13-add real-type y z)))
        (equal (amc20p13-add real-type x zero) x)
        (equal
         (amc20p13-add real-type x (amc20p13-neg real-type x))
         zero)
        (equal
         (amc20p13-mul real-type x y)
         (amc20p13-mul real-type y x))
        (equal
         (amc20p13-mul real-type (amc20p13-mul real-type x y) z)
         (amc20p13-mul real-type x (amc20p13-mul real-type y z)))
        (equal (amc20p13-mul real-type x one) x)
        (equal
         (amc20p13-mul
          real-type x (amc20p13-add real-type y z))
         (amc20p13-add
          real-type
          (amc20p13-mul real-type x y)
          (amc20p13-mul real-type x z)))
        (equal (amc20p13-inv real-type zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (amc20p13-mul real-type x (amc20p13-inv real-type x))
          one)))))))

(defun-sk amc20p13-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc20p13-real-p real-type x)
      (amc20p13-real-p real-type y)
      (amc20p13-real-p real-type z))
     (let ((zero (amc20p13-zero real-type)))
       (and
        (amc20p13-le real-type x x)
        (implies
         (and
          (amc20p13-le real-type x y)
          (amc20p13-le real-type y x))
         (equal x y))
        (implies
         (and
          (amc20p13-le real-type x y)
          (amc20p13-le real-type y z))
         (amc20p13-le real-type x z))
        (or
         (amc20p13-le real-type x y)
         (amc20p13-le real-type y x))
        (implies
         (amc20p13-le real-type x y)
         (amc20p13-le
          real-type
          (amc20p13-add real-type x z)
          (amc20p13-add real-type y z)))
        (implies
         (and
          (amc20p13-le real-type zero x)
          (amc20p13-le real-type zero y))
         (amc20p13-le
          real-type zero (amc20p13-mul real-type x y))))))))

(defun-sk amc20p13-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (amc20p13-real-p
       real-type (amc20p13-of-rational real-type p))
      (equal
       (amc20p13-of-rational real-type 0)
       (amc20p13-zero real-type))
      (equal
       (amc20p13-of-rational real-type 1)
       (amc20p13-one real-type))
      (equal
       (amc20p13-of-rational real-type (+ p q))
       (amc20p13-add
        real-type
        (amc20p13-of-rational real-type p)
        (amc20p13-of-rational real-type q)))
      (equal
       (amc20p13-of-rational real-type (* p q))
       (amc20p13-mul
        real-type
        (amc20p13-of-rational real-type p)
        (amc20p13-of-rational real-type q)))
      (iff
       (equal p q)
       (equal
        (amc20p13-of-rational real-type p)
        (amc20p13-of-rational real-type q)))
      (iff
       (<= p q)
       (amc20p13-le
        real-type
        (amc20p13-of-rational real-type p)
        (amc20p13-of-rational real-type q)))))))

(defun-sk amc20p13-rpow-laws-p (real-type)
  (forall (x y exponent other-exponent)
    (implies
     (and
      (amc20p13-positive-p real-type x)
      (amc20p13-positive-p real-type y)
      (amc20p13-real-p real-type exponent)
      (amc20p13-real-p real-type other-exponent))
     (and
      (amc20p13-positive-p
       real-type (amc20p13-rpow real-type x exponent))
      (equal
       (amc20p13-rpow
        real-type
        x
        (amc20p13-add real-type exponent other-exponent))
       (amc20p13-mul
        real-type
        (amc20p13-rpow real-type x exponent)
        (amc20p13-rpow real-type x other-exponent)))
      (equal
       (amc20p13-rpow
        real-type
        (amc20p13-mul real-type x y)
        exponent)
       (amc20p13-mul
        real-type
        (amc20p13-rpow real-type x exponent)
        (amc20p13-rpow real-type y exponent)))))))

(defun amc20p13-real-power-structure-p (real-type)
  (and
   (amc20p13-closure-laws-p real-type)
   (amc20p13-field-laws-p real-type)
   (amc20p13-order-laws-p real-type)
   (amc20p13-rational-laws-p real-type)
   (amc20p13-rpow-laws-p real-type)))

(defun amc20p13-nested-power (real-type a b c n)
  (amc20p13-rpow
   real-type
   (amc20p13-mul
    real-type
    n
    (amc20p13-rpow
     real-type
     (amc20p13-mul
      real-type
      n
      (amc20p13-rpow
       real-type
       n
       (amc20p13-unit-fraction real-type c)))
     (amc20p13-unit-fraction real-type b)))
   (amc20p13-unit-fraction real-type a)))

(defun amc12a-2020-p13-statement (real-type a b c n)
  (implies
   (and
    (amc20p13-real-power-structure-p real-type)
    (natp a)
    (natp b)
    (natp c)
    (< 1 a)
    (< 1 b)
    (< 1 c)
    (amc20p13-positive-p real-type n)
    (not (equal n (amc20p13-one real-type)))
    (equal
     (amc20p13-nested-power real-type a b c n)
     (amc20p13-rpow
      real-type
      (amc20p13-natural-power real-type n 25)
      (amc20p13-unit-fraction real-type 36))))
   (equal b 3)))

(value-triple :itpeval-statement-checked)
:q
