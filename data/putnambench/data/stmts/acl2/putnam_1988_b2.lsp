;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_b2:
;; for arbitrary real x and nonnegative real y, the displayed quadratic
;; hypothesis implies the displayed quadratic conclusion. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar interface presents an arbitrary real-closed ordered field.
;; Every variable below ranges directly over its carrier. The final formula is
;; first-order in the ordered-field language, so real-closed-field transfer
;; makes its universal closure equivalent to the source statement over R.

(defstub putnam-1988-b2-real-p (real-type value) t)
(defstub putnam-1988-b2-zero (real-type) t)
(defstub putnam-1988-b2-one (real-type) t)
(defstub putnam-1988-b2-add (real-type left right) t)
(defstub putnam-1988-b2-mul (real-type left right) t)
(defstub putnam-1988-b2-neg (real-type value) t)
(defstub putnam-1988-b2-inv (real-type value) t)
(defstub putnam-1988-b2-less (real-type left right) t)

(defun putnam-1988-b2-leq (real-type left right)
  (not (putnam-1988-b2-less real-type right left)))

(defun-sk putnam-1988-b2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1988-b2-real-p real-type x)
      (putnam-1988-b2-real-p real-type y)
      (putnam-1988-b2-real-p real-type z))
     (let* ((zero (putnam-1988-b2-zero real-type))
            (one (putnam-1988-b2-one real-type))
            (x-plus-y (putnam-1988-b2-add real-type x y))
            (y-plus-z (putnam-1988-b2-add real-type y z))
            (x-times-y (putnam-1988-b2-mul real-type x y))
            (y-times-z (putnam-1988-b2-mul real-type y z))
            (minus-x (putnam-1988-b2-neg real-type x))
            (inverse-x (putnam-1988-b2-inv real-type x)))
       (and
        (putnam-1988-b2-real-p real-type x-plus-y)
        (putnam-1988-b2-real-p real-type x-times-y)
        (putnam-1988-b2-real-p real-type minus-x)
        (putnam-1988-b2-real-p real-type inverse-x)
        (equal
         (putnam-1988-b2-add real-type x-plus-y z)
         (putnam-1988-b2-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1988-b2-add real-type y x))
        (equal (putnam-1988-b2-add real-type x zero) x)
        (equal (putnam-1988-b2-add real-type x minus-x) zero)
        (equal
         (putnam-1988-b2-mul real-type x-times-y z)
         (putnam-1988-b2-mul real-type x y-times-z))
        (equal x-times-y (putnam-1988-b2-mul real-type y x))
        (equal (putnam-1988-b2-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1988-b2-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1988-b2-mul real-type x y-plus-z)
         (putnam-1988-b2-add
          real-type
          (putnam-1988-b2-mul real-type x y)
          (putnam-1988-b2-mul real-type x z))))))))

(defun-sk putnam-1988-b2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1988-b2-real-p real-type x)
      (putnam-1988-b2-real-p real-type y)
      (putnam-1988-b2-real-p real-type z))
     (let ((zero (putnam-1988-b2-zero real-type)))
       (and
        (not (putnam-1988-b2-less real-type x x))
        (or
         (putnam-1988-b2-less real-type x y)
         (equal x y)
         (putnam-1988-b2-less real-type y x))
        (implies
         (and
          (putnam-1988-b2-less real-type x y)
          (putnam-1988-b2-less real-type y z))
         (putnam-1988-b2-less real-type x z))
        (implies
         (putnam-1988-b2-less real-type x y)
         (putnam-1988-b2-less
          real-type
          (putnam-1988-b2-add real-type x z)
          (putnam-1988-b2-add real-type y z)))
        (implies
         (and
          (putnam-1988-b2-less real-type zero x)
          (putnam-1988-b2-less real-type zero y))
         (putnam-1988-b2-less
          real-type
          zero
          (putnam-1988-b2-mul real-type x y))))))))

(defun putnam-1988-b2-real-list-p (real-type values)
  (if (consp values)
      (and
       (putnam-1988-b2-real-p real-type (car values))
       (putnam-1988-b2-real-list-p real-type (cdr values)))
    (equal values nil)))

(defun putnam-1988-b2-polynomial-value
    (real-type coefficients x)
  (if (consp coefficients)
      (putnam-1988-b2-add
       real-type
       (car coefficients)
       (putnam-1988-b2-mul
        real-type
        x
        (putnam-1988-b2-polynomial-value
         real-type (cdr coefficients) x)))
    (putnam-1988-b2-zero real-type)))

(defun-sk putnam-1988-b2-square-root-exists-p
    (real-type x)
  (exists (root)
    (and
     (putnam-1988-b2-real-p real-type root)
     (putnam-1988-b2-leq
      real-type (putnam-1988-b2-zero real-type) root)
     (equal
      (putnam-1988-b2-mul real-type root root)
      x))))

(defun-sk putnam-1988-b2-square-root-property-p
    (real-type)
  (forall (x)
    (implies
     (and
      (putnam-1988-b2-real-p real-type x)
      (putnam-1988-b2-leq
       real-type (putnam-1988-b2-zero real-type) x))
     (putnam-1988-b2-square-root-exists-p
      real-type x))))

(defun putnam-1988-b2-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (true-listp coefficients)
   (<= 2 (len coefficients))
   (evenp (len coefficients))
   (putnam-1988-b2-real-list-p real-type coefficients)
   (not
    (equal
     (car (last coefficients))
     (putnam-1988-b2-zero real-type)))))

(defun-sk putnam-1988-b2-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (putnam-1988-b2-real-p real-type root)
     (equal
      (putnam-1988-b2-polynomial-value
       real-type coefficients root)
      (putnam-1988-b2-zero real-type)))))

(defun-sk putnam-1988-b2-odd-degree-root-property-p
    (real-type)
  (forall (coefficients)
    (implies
     (putnam-1988-b2-odd-degree-polynomial-p
      real-type coefficients)
     (putnam-1988-b2-polynomial-root-exists-p
      real-type coefficients))))

(defun putnam-1988-b2-real-closed-field-p (real-type)
  (let ((zero (putnam-1988-b2-zero real-type))
        (one (putnam-1988-b2-one real-type)))
    (and
     (putnam-1988-b2-real-p real-type zero)
     (putnam-1988-b2-real-p real-type one)
     (not (equal zero one))
     (putnam-1988-b2-field-laws-p real-type)
     (putnam-1988-b2-order-laws-p real-type)
     (putnam-1988-b2-less real-type zero one)
     (putnam-1988-b2-square-root-property-p real-type)
     (putnam-1988-b2-odd-degree-root-property-p real-type))))

(defun putnam-1988-b2-hypotheses-p (real-type x y)
  (let* ((zero (putnam-1988-b2-zero real-type))
         (one (putnam-1988-b2-one real-type))
         (x-plus-one (putnam-1988-b2-add real-type x one))
         (y-plus-one (putnam-1988-b2-add real-type y one)))
    (and
     (putnam-1988-b2-real-p real-type x)
     (putnam-1988-b2-real-p real-type y)
     (putnam-1988-b2-leq real-type zero y)
     (putnam-1988-b2-leq
      real-type
      (putnam-1988-b2-mul real-type y y-plus-one)
      (putnam-1988-b2-mul
       real-type x-plus-one x-plus-one)))))

(defun putnambench-putnam-1988-b2-statement
    (real-type x y)
  (let* ((one (putnam-1988-b2-one real-type))
         (y-minus-one
          (putnam-1988-b2-add
           real-type y (putnam-1988-b2-neg real-type one))))
    (implies
     (and
      (putnam-1988-b2-real-closed-field-p real-type)
      (putnam-1988-b2-hypotheses-p real-type x y))
     (putnam-1988-b2-leq
      real-type
      (putnam-1988-b2-mul real-type y y-minus-one)
      (putnam-1988-b2-mul real-type x x)))))

(value-triple :itpeval-statement-checked)
:q
