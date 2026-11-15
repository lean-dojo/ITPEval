;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_b1:
;; positive real dimensions satisfying the circle and equal-area equations
;; force the rectangle height to be 2/5. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar interface presents an arbitrary real-closed ordered field.
;; Unlike a fixed algebraic-number encoding, its carrier ranges over every
;; scalar in the field. The final assertion is first-order in the
;; ordered-field language, so real-closed-field transfer preserves the
;; proposition over the real numbers without narrowing b or h.

(defstub putnam-1986-b1-real-p (real-type value) t)
(defstub putnam-1986-b1-zero (real-type) t)
(defstub putnam-1986-b1-one (real-type) t)
(defstub putnam-1986-b1-add (real-type left right) t)
(defstub putnam-1986-b1-mul (real-type left right) t)
(defstub putnam-1986-b1-neg (real-type value) t)
(defstub putnam-1986-b1-inv (real-type value) t)
(defstub putnam-1986-b1-less (real-type left right) t)

(defun putnam-1986-b1-leq (real-type left right)
  (not (putnam-1986-b1-less real-type right left)))

(defun putnam-1986-b1-sub (real-type left right)
  (putnam-1986-b1-add
   real-type left (putnam-1986-b1-neg real-type right)))

(defun putnam-1986-b1-div (real-type numerator denominator)
  (putnam-1986-b1-mul
   real-type numerator (putnam-1986-b1-inv real-type denominator)))

(defun-sk putnam-1986-b1-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1986-b1-real-p real-type x)
      (putnam-1986-b1-real-p real-type y)
      (putnam-1986-b1-real-p real-type z))
     (let* ((zero (putnam-1986-b1-zero real-type))
            (one (putnam-1986-b1-one real-type))
            (x-plus-y (putnam-1986-b1-add real-type x y))
            (y-plus-z (putnam-1986-b1-add real-type y z))
            (x-times-y (putnam-1986-b1-mul real-type x y))
            (y-times-z (putnam-1986-b1-mul real-type y z))
            (minus-x (putnam-1986-b1-neg real-type x))
            (inverse-x (putnam-1986-b1-inv real-type x)))
       (and
        (putnam-1986-b1-real-p real-type x-plus-y)
        (putnam-1986-b1-real-p real-type x-times-y)
        (putnam-1986-b1-real-p real-type minus-x)
        (putnam-1986-b1-real-p real-type inverse-x)
        (equal
         (putnam-1986-b1-add real-type x-plus-y z)
         (putnam-1986-b1-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1986-b1-add real-type y x))
        (equal (putnam-1986-b1-add real-type x zero) x)
        (equal (putnam-1986-b1-add real-type x minus-x) zero)
        (equal
         (putnam-1986-b1-mul real-type x-times-y z)
         (putnam-1986-b1-mul real-type x y-times-z))
        (equal x-times-y (putnam-1986-b1-mul real-type y x))
        (equal (putnam-1986-b1-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1986-b1-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1986-b1-mul real-type x y-plus-z)
         (putnam-1986-b1-add
          real-type
          (putnam-1986-b1-mul real-type x y)
          (putnam-1986-b1-mul real-type x z))))))))

(defun-sk putnam-1986-b1-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1986-b1-real-p real-type x)
      (putnam-1986-b1-real-p real-type y)
      (putnam-1986-b1-real-p real-type z))
     (let ((zero (putnam-1986-b1-zero real-type)))
       (and
        (not (putnam-1986-b1-less real-type x x))
        (or
         (putnam-1986-b1-less real-type x y)
         (equal x y)
         (putnam-1986-b1-less real-type y x))
        (implies
         (and
          (putnam-1986-b1-less real-type x y)
          (putnam-1986-b1-less real-type y z))
         (putnam-1986-b1-less real-type x z))
        (implies
         (putnam-1986-b1-less real-type x y)
         (putnam-1986-b1-less
          real-type
          (putnam-1986-b1-add real-type x z)
          (putnam-1986-b1-add real-type y z)))
        (implies
         (and
          (putnam-1986-b1-less real-type zero x)
          (putnam-1986-b1-less real-type zero y))
         (putnam-1986-b1-less
          real-type
          zero
          (putnam-1986-b1-mul real-type x y))))))))

(defun putnam-1986-b1-real-list-p (real-type values)
  (if (consp values)
      (and
       (putnam-1986-b1-real-p real-type (car values))
       (putnam-1986-b1-real-list-p real-type (cdr values)))
    (equal values nil)))

(defun putnam-1986-b1-polynomial-value
    (real-type coefficients x)
  (if (consp coefficients)
      (putnam-1986-b1-add
       real-type
       (car coefficients)
       (putnam-1986-b1-mul
        real-type
        x
        (putnam-1986-b1-polynomial-value
         real-type (cdr coefficients) x)))
    (putnam-1986-b1-zero real-type)))

(defun-sk putnam-1986-b1-square-root-exists-p
    (real-type x)
  (exists (root)
    (and
     (putnam-1986-b1-real-p real-type root)
     (putnam-1986-b1-leq
      real-type (putnam-1986-b1-zero real-type) root)
     (equal
      (putnam-1986-b1-mul real-type root root)
      x))))

(defun-sk putnam-1986-b1-square-root-property-p
    (real-type)
  (forall (x)
    (implies
     (and
      (putnam-1986-b1-real-p real-type x)
      (putnam-1986-b1-leq
       real-type (putnam-1986-b1-zero real-type) x))
     (putnam-1986-b1-square-root-exists-p
      real-type x))))

(defun putnam-1986-b1-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (true-listp coefficients)
   (<= 2 (len coefficients))
   (evenp (len coefficients))
   (putnam-1986-b1-real-list-p real-type coefficients)
   (not
    (equal
     (car (last coefficients))
     (putnam-1986-b1-zero real-type)))))

(defun-sk putnam-1986-b1-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (putnam-1986-b1-real-p real-type root)
     (equal
      (putnam-1986-b1-polynomial-value
       real-type coefficients root)
      (putnam-1986-b1-zero real-type)))))

(defun-sk putnam-1986-b1-odd-degree-root-property-p
    (real-type)
  (forall (coefficients)
    (implies
     (putnam-1986-b1-odd-degree-polynomial-p
      real-type coefficients)
     (putnam-1986-b1-polynomial-root-exists-p
      real-type coefficients))))

(defun putnam-1986-b1-real-closed-field-p (real-type)
  (let ((zero (putnam-1986-b1-zero real-type))
        (one (putnam-1986-b1-one real-type)))
    (and
     (putnam-1986-b1-real-p real-type zero)
     (putnam-1986-b1-real-p real-type one)
     (not (equal zero one))
     (putnam-1986-b1-field-laws-p real-type)
     (putnam-1986-b1-order-laws-p real-type)
     (putnam-1986-b1-less real-type zero one)
     (putnam-1986-b1-square-root-property-p real-type)
     (putnam-1986-b1-odd-degree-root-property-p real-type))))

(defun putnam-1986-b1-natural (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1986-b1-zero real-type)
    (putnam-1986-b1-add
     real-type
     (putnam-1986-b1-one real-type)
     (putnam-1986-b1-natural real-type (- n 1)))))

(defun putnam-1986-b1-hypotheses-p (real-type b h)
  (let* ((zero (putnam-1986-b1-zero real-type))
         (one (putnam-1986-b1-one real-type))
         (two (putnam-1986-b1-natural real-type 2))
         (half (putnam-1986-b1-div real-type one two)))
    (and
     (putnam-1986-b1-real-p real-type b)
     (putnam-1986-b1-real-p real-type h)
     (putnam-1986-b1-less real-type zero b)
     (putnam-1986-b1-less real-type zero h)
     (equal
      (putnam-1986-b1-add
       real-type
       (putnam-1986-b1-mul real-type b b)
       (putnam-1986-b1-mul real-type h h))
      (putnam-1986-b1-mul real-type two two))
     (equal
      (putnam-1986-b1-mul real-type b h)
      (putnam-1986-b1-mul
       real-type
       (putnam-1986-b1-mul real-type half b)
       (putnam-1986-b1-sub
        real-type one
        (putnam-1986-b1-div real-type h two)))))))

(defun putnambench-putnam-1986-b1-statement (real-type b h)
  (implies
   (and
    (putnam-1986-b1-real-closed-field-p real-type)
    (putnam-1986-b1-hypotheses-p real-type b h))
   (equal
    h
    (putnam-1986-b1-div
     real-type
     (putnam-1986-b1-natural real-type 2)
     (putnam-1986-b1-natural real-type 5)))))

(value-triple :itpeval-statement-checked)
:q
