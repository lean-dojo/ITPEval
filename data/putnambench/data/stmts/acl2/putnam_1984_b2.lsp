;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_b2:
;; the minimum of (u-v)^2+(sqrt(2-u^2)-9/v)^2 over
;; 0<u<sqrt(2) and v>0 is 8. This file contains no proof and does not choose
;; an attainment witness.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar interface presents an arbitrary real-closed ordered field.
;; The final assertion is first-order in the ordered-field language, so the
;; presentation is equivalent over every real-closed field and over R.

(defstub putnam-1984-b2-real-p (real-type value) t)
(defstub putnam-1984-b2-zero (real-type) t)
(defstub putnam-1984-b2-one (real-type) t)
(defstub putnam-1984-b2-add (real-type left right) t)
(defstub putnam-1984-b2-mul (real-type left right) t)
(defstub putnam-1984-b2-neg (real-type value) t)
(defstub putnam-1984-b2-inv (real-type value) t)
(defstub putnam-1984-b2-less (real-type left right) t)

(defun putnam-1984-b2-leq (real-type left right)
  (not (putnam-1984-b2-less real-type right left)))

(defun putnam-1984-b2-sub (real-type left right)
  (putnam-1984-b2-add
   real-type left (putnam-1984-b2-neg real-type right)))

(defun putnam-1984-b2-div (real-type numerator denominator)
  (putnam-1984-b2-mul
   real-type numerator (putnam-1984-b2-inv real-type denominator)))

(defun-sk putnam-1984-b2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1984-b2-real-p real-type x)
      (putnam-1984-b2-real-p real-type y)
      (putnam-1984-b2-real-p real-type z))
     (let* ((zero (putnam-1984-b2-zero real-type))
            (one (putnam-1984-b2-one real-type))
            (x-plus-y (putnam-1984-b2-add real-type x y))
            (y-plus-z (putnam-1984-b2-add real-type y z))
            (x-times-y (putnam-1984-b2-mul real-type x y))
            (y-times-z (putnam-1984-b2-mul real-type y z))
            (minus-x (putnam-1984-b2-neg real-type x))
            (inverse-x (putnam-1984-b2-inv real-type x)))
       (and
        (putnam-1984-b2-real-p real-type x-plus-y)
        (putnam-1984-b2-real-p real-type x-times-y)
        (putnam-1984-b2-real-p real-type minus-x)
        (putnam-1984-b2-real-p real-type inverse-x)
        (equal
         (putnam-1984-b2-add real-type x-plus-y z)
         (putnam-1984-b2-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1984-b2-add real-type y x))
        (equal (putnam-1984-b2-add real-type x zero) x)
        (equal (putnam-1984-b2-add real-type x minus-x) zero)
        (equal
         (putnam-1984-b2-mul real-type x-times-y z)
         (putnam-1984-b2-mul real-type x y-times-z))
        (equal x-times-y (putnam-1984-b2-mul real-type y x))
        (equal (putnam-1984-b2-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1984-b2-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1984-b2-mul real-type x y-plus-z)
         (putnam-1984-b2-add
          real-type
          (putnam-1984-b2-mul real-type x y)
          (putnam-1984-b2-mul real-type x z))))))))

(defun-sk putnam-1984-b2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1984-b2-real-p real-type x)
      (putnam-1984-b2-real-p real-type y)
      (putnam-1984-b2-real-p real-type z))
     (let ((zero (putnam-1984-b2-zero real-type)))
       (and
        (not (putnam-1984-b2-less real-type x x))
        (or
         (putnam-1984-b2-less real-type x y)
         (equal x y)
         (putnam-1984-b2-less real-type y x))
        (implies
         (and
          (putnam-1984-b2-less real-type x y)
          (putnam-1984-b2-less real-type y z))
         (putnam-1984-b2-less real-type x z))
        (implies
         (putnam-1984-b2-less real-type x y)
         (putnam-1984-b2-less
          real-type
          (putnam-1984-b2-add real-type x z)
          (putnam-1984-b2-add real-type y z)))
        (implies
         (and
          (putnam-1984-b2-less real-type zero x)
          (putnam-1984-b2-less real-type zero y))
         (putnam-1984-b2-less
          real-type
          zero
          (putnam-1984-b2-mul real-type x y))))))))

(defun putnam-1984-b2-real-list-p (real-type values)
  (if (consp values)
      (and
       (putnam-1984-b2-real-p real-type (car values))
       (putnam-1984-b2-real-list-p real-type (cdr values)))
    (equal values nil)))

(defun putnam-1984-b2-polynomial-value
    (real-type coefficients x)
  (if (consp coefficients)
      (putnam-1984-b2-add
       real-type
       (car coefficients)
       (putnam-1984-b2-mul
        real-type
        x
        (putnam-1984-b2-polynomial-value
         real-type (cdr coefficients) x)))
    (putnam-1984-b2-zero real-type)))

(defun-sk putnam-1984-b2-square-root-exists-p
    (real-type x)
  (exists (root)
    (and
     (putnam-1984-b2-real-p real-type root)
     (putnam-1984-b2-leq
      real-type (putnam-1984-b2-zero real-type) root)
     (equal
      (putnam-1984-b2-mul real-type root root)
      x))))

(defun-sk putnam-1984-b2-square-root-property-p
    (real-type)
  (forall (x)
    (implies
     (and
      (putnam-1984-b2-real-p real-type x)
      (putnam-1984-b2-leq
       real-type (putnam-1984-b2-zero real-type) x))
     (putnam-1984-b2-square-root-exists-p
      real-type x))))

(defun putnam-1984-b2-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (true-listp coefficients)
   (<= 2 (len coefficients))
   (evenp (len coefficients))
   (putnam-1984-b2-real-list-p real-type coefficients)
   (not
    (equal
     (car (last coefficients))
     (putnam-1984-b2-zero real-type)))))

(defun-sk putnam-1984-b2-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (putnam-1984-b2-real-p real-type root)
     (equal
      (putnam-1984-b2-polynomial-value
       real-type coefficients root)
      (putnam-1984-b2-zero real-type)))))

(defun-sk putnam-1984-b2-odd-degree-root-property-p
    (real-type)
  (forall (coefficients)
    (implies
     (putnam-1984-b2-odd-degree-polynomial-p
      real-type coefficients)
     (putnam-1984-b2-polynomial-root-exists-p
      real-type coefficients))))

(defun putnam-1984-b2-real-closed-field-p (real-type)
  (let ((zero (putnam-1984-b2-zero real-type))
        (one (putnam-1984-b2-one real-type)))
    (and
     (putnam-1984-b2-real-p real-type zero)
     (putnam-1984-b2-real-p real-type one)
     (not (equal zero one))
     (putnam-1984-b2-field-laws-p real-type)
     (putnam-1984-b2-order-laws-p real-type)
     (putnam-1984-b2-less real-type zero one)
     (putnam-1984-b2-square-root-property-p real-type)
     (putnam-1984-b2-odd-degree-root-property-p real-type))))

(defun putnam-1984-b2-natural (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1984-b2-zero real-type)
    (putnam-1984-b2-add
     real-type
     (putnam-1984-b2-one real-type)
     (putnam-1984-b2-natural real-type (- n 1)))))

;; On 0<u<sqrt(2), w=sqrt(2-u^2) is equivalently the unique positive w
;; satisfying u^2+w^2=2. This removes only a definitional square root, while
;; retaining all real points of the source domain.

(defun putnam-1984-b2-domain-p (real-type u w v)
  (let ((zero (putnam-1984-b2-zero real-type))
        (two (putnam-1984-b2-natural real-type 2)))
    (and
     (putnam-1984-b2-real-p real-type u)
     (putnam-1984-b2-real-p real-type w)
     (putnam-1984-b2-real-p real-type v)
     (putnam-1984-b2-less real-type zero u)
     (putnam-1984-b2-less real-type zero w)
     (putnam-1984-b2-less real-type zero v)
     (equal
      (putnam-1984-b2-add
       real-type
       (putnam-1984-b2-mul real-type u u)
       (putnam-1984-b2-mul real-type w w))
      two))))

(defun putnam-1984-b2-value (real-type u w v)
  (let* ((nine (putnam-1984-b2-natural real-type 9))
         (u-minus-v (putnam-1984-b2-sub real-type u v))
         (w-minus-nine-over-v
          (putnam-1984-b2-sub
           real-type
           w
           (putnam-1984-b2-div real-type nine v))))
    (putnam-1984-b2-add
     real-type
     (putnam-1984-b2-mul
      real-type u-minus-v u-minus-v)
     (putnam-1984-b2-mul
      real-type
      w-minus-nine-over-v
      w-minus-nine-over-v))))

(defun-sk putnam-1984-b2-lower-bound-p (real-type)
  (forall (u w v)
    (implies
     (putnam-1984-b2-domain-p real-type u w v)
     (putnam-1984-b2-leq
      real-type
      (putnam-1984-b2-natural real-type 8)
      (putnam-1984-b2-value real-type u w v)))))

(defun-sk putnam-1984-b2-attained-p (real-type)
  (exists (u w v)
    (and
     (putnam-1984-b2-domain-p real-type u w v)
     (equal
      (putnam-1984-b2-value real-type u w v)
      (putnam-1984-b2-natural real-type 8)))))

(defun putnambench-putnam-1984-b2-statement (real-type)
  (implies
   (putnam-1984-b2-real-closed-field-p real-type)
   (and
    (putnam-1984-b2-lower-bound-p real-type)
    (putnam-1984-b2-attained-p real-type))))

(value-triple :itpeval-statement-checked)
:q
