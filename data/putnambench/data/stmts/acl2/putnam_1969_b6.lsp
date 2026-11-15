;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_b6:
;; real 3-by-2 and 2-by-3 matrices whose product is the specified 3-by-3
;; matrix have reverse product equal to 9 times the 2-by-2 identity.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar domain is presented as an arbitrary real-closed ordered field.
;; This preserves the source domain because real-closed ordered fields have
;; the same first-order theory as the real numbers, and the matrix assertion
;; below is a first-order sentence in the ordered-field language. The source's
;; auxiliary matrix p is eliminated definitionally by substituting its nine
;; specified entries into A*B.

(defstub p69b6-real-p (real-type value) t)
(defstub p69b6-zero (real-type) t)
(defstub p69b6-one (real-type) t)
(defstub p69b6-add (real-type left right) t)
(defstub p69b6-mul (real-type left right) t)
(defstub p69b6-neg (real-type value) t)
(defstub p69b6-inv (real-type value) t)
(defstub p69b6-less (real-type left right) t)

(defun-sk p69b6-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p69b6-real-p real-type x)
      (p69b6-real-p real-type y)
      (p69b6-real-p real-type z))
     (let* ((zero (p69b6-zero real-type))
            (one (p69b6-one real-type))
            (xy-add (p69b6-add real-type x y))
            (yz-add (p69b6-add real-type y z))
            (xy-mul (p69b6-mul real-type x y))
            (yz-mul (p69b6-mul real-type y z))
            (neg-x (p69b6-neg real-type x))
            (inv-x (p69b6-inv real-type x)))
       (and
        (p69b6-real-p real-type xy-add)
        (p69b6-real-p real-type xy-mul)
        (p69b6-real-p real-type neg-x)
        (p69b6-real-p real-type inv-x)
        (equal (p69b6-add real-type xy-add z)
               (p69b6-add real-type x yz-add))
        (equal xy-add (p69b6-add real-type y x))
        (equal (p69b6-add real-type x zero) x)
        (equal (p69b6-add real-type x neg-x) zero)
        (equal (p69b6-mul real-type xy-mul z)
               (p69b6-mul real-type x yz-mul))
        (equal xy-mul (p69b6-mul real-type y x))
        (equal (p69b6-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (p69b6-mul real-type x inv-x) one))
        (equal
         (p69b6-mul real-type x yz-add)
         (p69b6-add
          real-type
          (p69b6-mul real-type x y)
          (p69b6-mul real-type x z))))))))

(defun-sk p69b6-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p69b6-real-p real-type x)
      (p69b6-real-p real-type y)
      (p69b6-real-p real-type z))
     (let ((zero (p69b6-zero real-type)))
       (and
        (not (p69b6-less real-type x x))
        (or
         (equal x y)
         (p69b6-less real-type x y)
         (p69b6-less real-type y x))
        (implies
         (and
          (p69b6-less real-type x y)
          (p69b6-less real-type y z))
         (p69b6-less real-type x z))
        (implies
         (p69b6-less real-type x y)
         (p69b6-less
          real-type
          (p69b6-add real-type x z)
          (p69b6-add real-type y z)))
        (implies
         (and
          (p69b6-less real-type zero x)
          (p69b6-less real-type zero y))
         (p69b6-less
          real-type
          zero
          (p69b6-mul real-type x y))))))))

(defun p69b6-real-list-p (real-type values)
  (if (consp values)
      (and
       (p69b6-real-p real-type (car values))
       (p69b6-real-list-p real-type (cdr values)))
    (equal values nil)))

;; Coefficients are in ascending order. This is Horner evaluation.
(defun p69b6-polynomial-value (real-type coefficients x)
  (if (consp coefficients)
      (p69b6-add
       real-type
       (car coefficients)
       (p69b6-mul
        real-type
        x
        (p69b6-polynomial-value
         real-type (cdr coefficients) x)))
    (p69b6-zero real-type)))

(defun-sk p69b6-square-root-exists-p (real-type x)
  (exists (root)
    (and
     (p69b6-real-p real-type root)
     (not
      (p69b6-less
       real-type root (p69b6-zero real-type)))
     (equal
      (p69b6-mul real-type root root)
      x))))

(defun-sk p69b6-nonnegative-square-root-property-p (real-type)
  (forall (x)
    (implies
     (and
      (p69b6-real-p real-type x)
      (not
       (p69b6-less
        real-type x (p69b6-zero real-type))))
     (p69b6-square-root-exists-p real-type x))))

(defun p69b6-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (true-listp coefficients)
   (<= 2 (len coefficients))
   (evenp (len coefficients))
   (p69b6-real-list-p real-type coefficients)
   (not
    (equal
     (car (last coefficients))
     (p69b6-zero real-type)))))

(defun-sk p69b6-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (p69b6-real-p real-type root)
     (equal
      (p69b6-polynomial-value
       real-type coefficients root)
      (p69b6-zero real-type)))))

(defun-sk p69b6-odd-degree-root-property-p (real-type)
  (forall (coefficients)
    (implies
     (p69b6-odd-degree-polynomial-p
      real-type coefficients)
     (p69b6-polynomial-root-exists-p
      real-type coefficients))))

(defun p69b6-real-closed-field-p (real-type)
  (let ((zero (p69b6-zero real-type))
        (one (p69b6-one real-type)))
    (and
     (p69b6-real-p real-type zero)
     (p69b6-real-p real-type one)
     (not (equal zero one))
     (p69b6-field-laws-p real-type)
     (p69b6-order-laws-p real-type)
     (p69b6-less real-type zero one)
     (p69b6-nonnegative-square-root-property-p real-type)
     (p69b6-odd-degree-root-property-p real-type))))

(defun p69b6-natural (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p69b6-zero real-type)
    (p69b6-add
     real-type
     (p69b6-one real-type)
     (p69b6-natural real-type (1- n)))))

(defun p69b6-sum2 (real-type x1 y1 x2 y2)
  (p69b6-add
   real-type
   (p69b6-mul real-type x1 y1)
   (p69b6-mul real-type x2 y2)))

(defun p69b6-sum3
    (real-type x1 y1 x2 y2 x3 y3)
  (p69b6-add
   real-type
   (p69b6-add
    real-type
    (p69b6-mul real-type x1 y1)
    (p69b6-mul real-type x2 y2))
   (p69b6-mul real-type x3 y3)))

(defun p69b6-matrix-entries-p
    (real-type
     a00 a01 a10 a11 a20 a21
     b00 b01 b02 b10 b11 b12)
  (and
   (p69b6-real-p real-type a00)
   (p69b6-real-p real-type a01)
   (p69b6-real-p real-type a10)
   (p69b6-real-p real-type a11)
   (p69b6-real-p real-type a20)
   (p69b6-real-p real-type a21)
   (p69b6-real-p real-type b00)
   (p69b6-real-p real-type b01)
   (p69b6-real-p real-type b02)
   (p69b6-real-p real-type b10)
   (p69b6-real-p real-type b11)
   (p69b6-real-p real-type b12)))

(defun p69b6-forward-product-p
    (real-type
     a00 a01 a10 a11 a20 a21
     b00 b01 b02 b10 b11 b12)
  (let ((two (p69b6-natural real-type 2))
        (four (p69b6-natural real-type 4))
        (five (p69b6-natural real-type 5))
        (eight (p69b6-natural real-type 8)))
    (and
     (equal (p69b6-sum2 real-type a00 b00 a01 b10)
            eight)
     (equal (p69b6-sum2 real-type a00 b01 a01 b11)
            two)
     (equal (p69b6-sum2 real-type a00 b02 a01 b12)
            (p69b6-neg real-type two))
     (equal (p69b6-sum2 real-type a10 b00 a11 b10)
            two)
     (equal (p69b6-sum2 real-type a10 b01 a11 b11)
            five)
     (equal (p69b6-sum2 real-type a10 b02 a11 b12)
            four)
     (equal (p69b6-sum2 real-type a20 b00 a21 b10)
            (p69b6-neg real-type two))
     (equal (p69b6-sum2 real-type a20 b01 a21 b11)
            four)
     (equal (p69b6-sum2 real-type a20 b02 a21 b12)
            five))))

(defun p69b6-reverse-product-p
    (real-type
     a00 a01 a10 a11 a20 a21
     b00 b01 b02 b10 b11 b12)
  (let ((zero (p69b6-zero real-type))
        (nine (p69b6-natural real-type 9)))
    (and
     (equal
      (p69b6-sum3
       real-type b00 a00 b01 a10 b02 a20)
      nine)
     (equal
      (p69b6-sum3
       real-type b00 a01 b01 a11 b02 a21)
      zero)
     (equal
      (p69b6-sum3
       real-type b10 a00 b11 a10 b12 a20)
      zero)
     (equal
      (p69b6-sum3
       real-type b10 a01 b11 a11 b12 a21)
      nine))))

(defun putnambench-putnam-1969-b6-statement
    (real-type
     a00 a01 a10 a11 a20 a21
     b00 b01 b02 b10 b11 b12)
  (implies
   (and
    (p69b6-real-closed-field-p real-type)
    (p69b6-matrix-entries-p
     real-type
     a00 a01 a10 a11 a20 a21
     b00 b01 b02 b10 b11 b12)
    (p69b6-forward-product-p
     real-type
     a00 a01 a10 a11 a20 a21
     b00 b01 b02 b10 b11 b12))
   (p69b6-reverse-product-p
    real-type
    a00 a01 a10 a11 a20 a21
    b00 b01 b02 b10 b11 b12)))

(value-triple :itpeval-statement-checked)
:q
