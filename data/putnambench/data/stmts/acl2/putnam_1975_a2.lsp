;; Statement-only formalization of PutnamBench corpus artifact putnam_1975_a2:
;; the real coefficient pairs for which every root of z^2+bz+c lies strictly
;; inside the complex unit disk. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative symbols below present an arbitrary real-closed ordered
;; field. Complex numbers are represented by pairs of field elements, and the
;; polynomial equation and squared-modulus inequality are expanded
;; definitionally. The resulting assertion is a first-order sentence in the
;; language of ordered fields. Completeness of the theory of real-closed
;; fields therefore transfers it bidirectionally between this representation
;; and its instance over the real numbers.

(defstub putnam-1975-a2-real-p (real-type value) t)
(defstub putnam-1975-a2-zero (real-type) t)
(defstub putnam-1975-a2-one (real-type) t)
(defstub putnam-1975-a2-add (real-type left right) t)
(defstub putnam-1975-a2-mul (real-type left right) t)
(defstub putnam-1975-a2-neg (real-type value) t)
(defstub putnam-1975-a2-inv (real-type value) t)
(defstub putnam-1975-a2-less (real-type left right) t)

(defun putnam-1975-a2-sub (real-type left right)
  (putnam-1975-a2-add
   real-type left (putnam-1975-a2-neg real-type right)))

(defun-sk putnam-1975-a2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1975-a2-real-p real-type x)
      (putnam-1975-a2-real-p real-type y)
      (putnam-1975-a2-real-p real-type z))
     (let* ((zero (putnam-1975-a2-zero real-type))
            (one (putnam-1975-a2-one real-type))
            (xy-add (putnam-1975-a2-add real-type x y))
            (yz-add (putnam-1975-a2-add real-type y z))
            (xy-mul (putnam-1975-a2-mul real-type x y))
            (yz-mul (putnam-1975-a2-mul real-type y z))
            (neg-x (putnam-1975-a2-neg real-type x))
            (inv-x (putnam-1975-a2-inv real-type x)))
       (and
        (putnam-1975-a2-real-p real-type xy-add)
        (putnam-1975-a2-real-p real-type xy-mul)
        (putnam-1975-a2-real-p real-type neg-x)
        (putnam-1975-a2-real-p real-type inv-x)
        (equal
         (putnam-1975-a2-add real-type xy-add z)
         (putnam-1975-a2-add real-type x yz-add))
        (equal xy-add (putnam-1975-a2-add real-type y x))
        (equal (putnam-1975-a2-add real-type x zero) x)
        (equal (putnam-1975-a2-add real-type x neg-x) zero)
        (equal
         (putnam-1975-a2-mul real-type xy-mul z)
         (putnam-1975-a2-mul real-type x yz-mul))
        (equal xy-mul (putnam-1975-a2-mul real-type y x))
        (equal (putnam-1975-a2-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1975-a2-mul real-type x inv-x)
          one))
        (equal
         (putnam-1975-a2-mul real-type x yz-add)
         (putnam-1975-a2-add
          real-type
          (putnam-1975-a2-mul real-type x y)
          (putnam-1975-a2-mul real-type x z))))))))

(defun-sk putnam-1975-a2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1975-a2-real-p real-type x)
      (putnam-1975-a2-real-p real-type y)
      (putnam-1975-a2-real-p real-type z))
     (let ((zero (putnam-1975-a2-zero real-type)))
       (and
        (not (putnam-1975-a2-less real-type x x))
        (or
         (equal x y)
         (putnam-1975-a2-less real-type x y)
         (putnam-1975-a2-less real-type y x))
        (implies
         (and
          (putnam-1975-a2-less real-type x y)
          (putnam-1975-a2-less real-type y z))
         (putnam-1975-a2-less real-type x z))
        (implies
         (putnam-1975-a2-less real-type x y)
         (putnam-1975-a2-less
          real-type
          (putnam-1975-a2-add real-type x z)
          (putnam-1975-a2-add real-type y z)))
        (implies
         (and
          (putnam-1975-a2-less real-type zero x)
          (putnam-1975-a2-less real-type zero y))
         (putnam-1975-a2-less
          real-type
          zero
          (putnam-1975-a2-mul real-type x y))))))))

(defun putnam-1975-a2-real-list-p (real-type values)
  (if (consp values)
      (and
       (putnam-1975-a2-real-p real-type (car values))
       (putnam-1975-a2-real-list-p real-type (cdr values)))
    (equal values nil)))

(defun putnam-1975-a2-polynomial-value
    (real-type coefficients x)
  (if (consp coefficients)
      (putnam-1975-a2-add
       real-type
       (car coefficients)
       (putnam-1975-a2-mul
        real-type
        x
        (putnam-1975-a2-polynomial-value
         real-type (cdr coefficients) x)))
    (putnam-1975-a2-zero real-type)))

(defun-sk putnam-1975-a2-square-root-exists-p
    (real-type x)
  (exists (root)
    (and
     (putnam-1975-a2-real-p real-type root)
     (not
      (putnam-1975-a2-less
       real-type root (putnam-1975-a2-zero real-type)))
     (equal
      (putnam-1975-a2-mul real-type root root)
      x))))

(defun-sk putnam-1975-a2-nonnegative-square-roots-p
    (real-type)
  (forall (x)
    (implies
     (and
      (putnam-1975-a2-real-p real-type x)
      (not
       (putnam-1975-a2-less
        real-type x (putnam-1975-a2-zero real-type))))
     (putnam-1975-a2-square-root-exists-p
      real-type x))))

(defun putnam-1975-a2-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (true-listp coefficients)
   (<= 2 (len coefficients))
   (evenp (len coefficients))
   (putnam-1975-a2-real-list-p real-type coefficients)
   (not
    (equal
     (car (last coefficients))
     (putnam-1975-a2-zero real-type)))))

(defun-sk putnam-1975-a2-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (putnam-1975-a2-real-p real-type root)
     (equal
      (putnam-1975-a2-polynomial-value
       real-type coefficients root)
      (putnam-1975-a2-zero real-type)))))

(defun-sk putnam-1975-a2-odd-degree-roots-p (real-type)
  (forall (coefficients)
    (implies
     (putnam-1975-a2-odd-degree-polynomial-p
      real-type coefficients)
     (putnam-1975-a2-polynomial-root-exists-p
      real-type coefficients))))

(defun putnam-1975-a2-real-closed-field-p (real-type)
  (let ((zero (putnam-1975-a2-zero real-type))
        (one (putnam-1975-a2-one real-type)))
    (and
     (putnam-1975-a2-real-p real-type zero)
     (putnam-1975-a2-real-p real-type one)
     (not (equal zero one))
     (putnam-1975-a2-field-laws-p real-type)
     (putnam-1975-a2-order-laws-p real-type)
     (putnam-1975-a2-less real-type zero one)
     (putnam-1975-a2-nonnegative-square-roots-p real-type)
     (putnam-1975-a2-odd-degree-roots-p real-type))))

(defun putnam-1975-a2-square (real-type x)
  (putnam-1975-a2-mul real-type x x))

(defun putnam-1975-a2-two (real-type)
  (putnam-1975-a2-add
   real-type
   (putnam-1975-a2-one real-type)
   (putnam-1975-a2-one real-type)))

(defun putnam-1975-a2-complex-root-p
    (real-type b c x y)
  (let* ((zero (putnam-1975-a2-zero real-type))
         (x-squared (putnam-1975-a2-square real-type x))
         (y-squared (putnam-1975-a2-square real-type y))
         (real-part
          (putnam-1975-a2-add
           real-type
           (putnam-1975-a2-add
            real-type
            (putnam-1975-a2-sub
             real-type x-squared y-squared)
            (putnam-1975-a2-mul real-type b x))
           c))
         (imaginary-part
          (putnam-1975-a2-add
           real-type
           (putnam-1975-a2-mul
            real-type
            (putnam-1975-a2-two real-type)
            (putnam-1975-a2-mul real-type x y))
           (putnam-1975-a2-mul real-type b y))))
    (and
     (equal real-part zero)
     (equal imaginary-part zero))))

(defun putnam-1975-a2-modulus-squared
    (real-type x y)
  (putnam-1975-a2-add
   real-type
   (putnam-1975-a2-square real-type x)
   (putnam-1975-a2-square real-type y)))

(defun-sk putnam-1975-a2-all-roots-inside-p
    (real-type b c)
  (forall (x y)
    (implies
     (and
      (putnam-1975-a2-real-p real-type x)
      (putnam-1975-a2-real-p real-type y)
      (putnam-1975-a2-complex-root-p
       real-type b c x y))
     (putnam-1975-a2-less
      real-type
      (putnam-1975-a2-modulus-squared
       real-type x y)
      (putnam-1975-a2-one real-type)))))

(defun putnam-1975-a2-solution-p (real-type b c)
  (let ((negative-one
         (putnam-1975-a2-neg
          real-type (putnam-1975-a2-one real-type))))
    (and
     (putnam-1975-a2-less
      real-type c (putnam-1975-a2-one real-type))
     (putnam-1975-a2-less
      real-type
      negative-one
      (putnam-1975-a2-sub real-type c b))
     (putnam-1975-a2-less
      real-type
      negative-one
      (putnam-1975-a2-add real-type c b)))))

(defun-sk putnam-1975-a2-characterization-p (real-type)
  (forall (b c)
    (implies
     (and
      (putnam-1975-a2-real-p real-type b)
      (putnam-1975-a2-real-p real-type c))
     (iff
      (putnam-1975-a2-all-roots-inside-p
       real-type b c)
      (putnam-1975-a2-solution-p
       real-type b c)))))

(defun putnambench-putnam-1975-a2-statement (real-type)
  (implies
   (putnam-1975-a2-real-closed-field-p real-type)
   (putnam-1975-a2-characterization-p real-type)))

(value-triple :itpeval-statement-checked)
:q
