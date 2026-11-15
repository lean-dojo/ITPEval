;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_a1:
;; the real coefficients for which two mutually defined quadratic curves are
;; tangent, characterized by four explicit values. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has no native carrier of all real numbers.  Following the
;; repository's statement-only convention, these conservative interfaces
;; describe an arbitrary real closed ordered field.  Every carrier, field,
;; order, and real-closedness law used below is an explicit hypothesis of the
;; statement predicate.  The source formula is first-order in the ordered-field
;; language, so the completeness of real closed fields gives a bidirectional
;; equivalence with its interpretation over the real numbers.
;;
;; P is inlined using P_def.  Thus alpha is still an arbitrary real-field
;; element, while the tangency witnesses x and y remain existentially
;; quantified inside the statement.  The last quadratic has precisely the
;; roots (13 + sqrt(601))/12 and (13 - sqrt(601))/12 in every real closed
;; ordered field.

(defstub putnam-2007-a1-real-p (real-type value) t)
(defstub putnam-2007-a1-zero (real-type) t)
(defstub putnam-2007-a1-one (real-type) t)
(defstub putnam-2007-a1-add (real-type left right) t)
(defstub putnam-2007-a1-mul (real-type left right) t)
(defstub putnam-2007-a1-neg (real-type value) t)
(defstub putnam-2007-a1-inv (real-type value) t)
(defstub putnam-2007-a1-less (real-type left right) t)

(defun putnam-2007-a1-sub (real-type left right)
  (putnam-2007-a1-add
   real-type
   left
   (putnam-2007-a1-neg real-type right)))

(defun putnam-2007-a1-div (real-type numerator denominator)
  (putnam-2007-a1-mul
   real-type
   numerator
   (putnam-2007-a1-inv real-type denominator)))

(defun putnam-2007-a1-r-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-2007-a1-zero real-type)
    (putnam-2007-a1-add
     real-type
     (putnam-2007-a1-one real-type)
     (putnam-2007-a1-r-nat real-type (1- n)))))

;; Explicit ordered-field laws.

(defun-sk putnam-2007-a1-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-2007-a1-real-p real-type x)
      (putnam-2007-a1-real-p real-type y)
      (putnam-2007-a1-real-p real-type z))
     (let* ((zero (putnam-2007-a1-zero real-type))
            (one (putnam-2007-a1-one real-type))
            (x-plus-y (putnam-2007-a1-add real-type x y))
            (y-plus-z (putnam-2007-a1-add real-type y z))
            (x-times-y (putnam-2007-a1-mul real-type x y))
            (y-times-z (putnam-2007-a1-mul real-type y z))
            (minus-x (putnam-2007-a1-neg real-type x))
            (inverse-x (putnam-2007-a1-inv real-type x)))
       (and
        (putnam-2007-a1-real-p real-type x-plus-y)
        (putnam-2007-a1-real-p real-type x-times-y)
        (putnam-2007-a1-real-p real-type minus-x)
        (putnam-2007-a1-real-p real-type inverse-x)
        (equal
         (putnam-2007-a1-add real-type x-plus-y z)
         (putnam-2007-a1-add real-type x y-plus-z))
        (equal
         x-plus-y
         (putnam-2007-a1-add real-type y x))
        (equal
         (putnam-2007-a1-add real-type x zero)
         x)
        (equal
         (putnam-2007-a1-add real-type x minus-x)
         zero)
        (equal
         (putnam-2007-a1-mul real-type x-times-y z)
         (putnam-2007-a1-mul real-type x y-times-z))
        (equal
         x-times-y
         (putnam-2007-a1-mul real-type y x))
        (equal
         (putnam-2007-a1-mul real-type x one)
         x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-2007-a1-mul real-type x inverse-x)
          one))
        (equal
         (putnam-2007-a1-mul real-type x y-plus-z)
         (putnam-2007-a1-add
          real-type
          (putnam-2007-a1-mul real-type x y)
          (putnam-2007-a1-mul real-type x z))))))))

(defun-sk putnam-2007-a1-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-2007-a1-real-p real-type x)
      (putnam-2007-a1-real-p real-type y)
      (putnam-2007-a1-real-p real-type z))
     (let ((zero (putnam-2007-a1-zero real-type)))
       (and
        (not (putnam-2007-a1-less real-type x x))
        (or
         (putnam-2007-a1-less real-type x y)
         (equal x y)
         (putnam-2007-a1-less real-type y x))
        (implies
         (and
          (putnam-2007-a1-less real-type x y)
          (putnam-2007-a1-less real-type y z))
         (putnam-2007-a1-less real-type x z))
        (implies
         (putnam-2007-a1-less real-type x y)
         (putnam-2007-a1-less
          real-type
          (putnam-2007-a1-add real-type x z)
          (putnam-2007-a1-add real-type y z)))
        (implies
         (and
          (putnam-2007-a1-less real-type zero x)
          (putnam-2007-a1-less real-type zero y))
         (putnam-2007-a1-less
          real-type
          zero
          (putnam-2007-a1-mul real-type x y))))))))

;; The square-root and odd-degree-root properties are the standard algebraic
;; characterization of real closed ordered fields.

(defun-sk putnam-2007-a1-square-root-exists-p
    (real-type value)
  (exists (root)
    (and
     (putnam-2007-a1-real-p real-type root)
     (equal
      (putnam-2007-a1-mul real-type root root)
      value))))

(defun-sk putnam-2007-a1-square-root-law-p (real-type)
  (forall (value)
    (implies
     (and
      (putnam-2007-a1-real-p real-type value)
      (not
       (putnam-2007-a1-less
        real-type
        value
        (putnam-2007-a1-zero real-type))))
     (putnam-2007-a1-square-root-exists-p
      real-type value))))

(defun putnam-2007-a1-coefficient-list-p
    (real-type coefficients)
  (if (consp coefficients)
      (and
       (putnam-2007-a1-real-p
        real-type (car coefficients))
       (putnam-2007-a1-coefficient-list-p
        real-type (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients are in ascending degree order.
(defun putnam-2007-a1-polynomial-p
    (real-type coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-2007-a1-coefficient-list-p
    real-type coefficients)
   (not
    (equal
     (car (last coefficients))
     (putnam-2007-a1-zero real-type)))))

(defun putnam-2007-a1-polynomial-eval
    (real-type coefficients value)
  (if (consp coefficients)
      (putnam-2007-a1-add
       real-type
       (car coefficients)
       (putnam-2007-a1-mul
        real-type
        value
        (putnam-2007-a1-polynomial-eval
         real-type (cdr coefficients) value)))
    (putnam-2007-a1-zero real-type)))

(defun-sk putnam-2007-a1-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (putnam-2007-a1-real-p real-type root)
     (equal
      (putnam-2007-a1-polynomial-eval
       real-type coefficients root)
      (putnam-2007-a1-zero real-type)))))

(defun-sk putnam-2007-a1-odd-degree-root-law-p (real-type)
  (forall (coefficients)
    (implies
     (and
      (putnam-2007-a1-polynomial-p
       real-type coefficients)
      (evenp (len coefficients)))
     (putnam-2007-a1-polynomial-root-exists-p
      real-type coefficients))))

(defun putnam-2007-a1-real-closed-field-p (real-type)
  (let ((zero (putnam-2007-a1-zero real-type))
        (one (putnam-2007-a1-one real-type)))
    (and
     (putnam-2007-a1-real-p real-type zero)
     (putnam-2007-a1-real-p real-type one)
     (not (equal zero one))
     (putnam-2007-a1-field-laws-p real-type)
     (putnam-2007-a1-order-laws-p real-type)
     (putnam-2007-a1-less real-type zero one)
     (putnam-2007-a1-square-root-law-p real-type)
     (putnam-2007-a1-odd-degree-root-law-p real-type))))

;; The quadratic and its derivative, interpreted in the represented real field.

(defun putnam-2007-a1-quadratic
    (real-type alpha value)
  (putnam-2007-a1-add
   real-type
   (putnam-2007-a1-add
    real-type
    (putnam-2007-a1-mul
     real-type
     alpha
     (putnam-2007-a1-mul real-type value value))
    (putnam-2007-a1-mul real-type alpha value))
   (putnam-2007-a1-div
    real-type
    (putnam-2007-a1-one real-type)
    (putnam-2007-a1-r-nat real-type 24))))

(defun putnam-2007-a1-quadratic-derivative
    (real-type alpha value)
  (putnam-2007-a1-add
   real-type
   (putnam-2007-a1-mul
    real-type
    (putnam-2007-a1-r-nat real-type 2)
    (putnam-2007-a1-mul real-type alpha value))
   alpha))

(defun-sk putnam-2007-a1-tangent-p
    (real-type alpha)
  (exists (x y)
    (and
     (putnam-2007-a1-real-p real-type x)
     (putnam-2007-a1-real-p real-type y)
     (equal
      (putnam-2007-a1-quadratic real-type alpha x)
      y)
     (equal
      (putnam-2007-a1-quadratic real-type alpha y)
      x)
     (equal
      (putnam-2007-a1-mul
       real-type
       (putnam-2007-a1-quadratic-derivative
        real-type alpha x)
       (putnam-2007-a1-quadratic-derivative
        real-type alpha y))
      (putnam-2007-a1-one real-type)))))

(defun putnam-2007-a1-solution-p
    (real-type alpha)
  (let ((two (putnam-2007-a1-r-nat real-type 2))
        (three (putnam-2007-a1-r-nat real-type 3))
        (six (putnam-2007-a1-r-nat real-type 6))
        (thirteen (putnam-2007-a1-r-nat real-type 13))
        (eighteen (putnam-2007-a1-r-nat real-type 18))
        (zero (putnam-2007-a1-zero real-type)))
    (or
     (equal
      alpha
      (putnam-2007-a1-div real-type two three))
     (equal
      alpha
      (putnam-2007-a1-div real-type three two))
     (equal
      (putnam-2007-a1-sub
       real-type
       (putnam-2007-a1-sub
        real-type
        (putnam-2007-a1-mul
         real-type
         six
         (putnam-2007-a1-mul real-type alpha alpha))
        (putnam-2007-a1-mul
         real-type thirteen alpha))
       eighteen)
      zero))))

(defun putnambench-putnam-2007-a1-statement
    (real-type alpha)
  (implies
   (and
    (putnam-2007-a1-real-closed-field-p real-type)
    (putnam-2007-a1-real-p real-type alpha))
   (iff
    (putnam-2007-a1-tangent-p real-type alpha)
    (putnam-2007-a1-solution-p real-type alpha))))

(value-triple :itpeval-statement-checked)
:q
