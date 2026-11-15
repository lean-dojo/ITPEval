;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_b2:
;; the real parameters c for which a straight line intersects
;; x^4+9*x^3+c*x^2+9*x+4 in exactly four distinct points. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative interfaces below present an arbitrary real-closed ordered
;; field. Every carrier, field, order, square-root, and odd-degree-root law is
;; explicit in the statement predicates. The source biconditional is a
;; first-order ordered-field formula with rational coefficients, so
;; completeness of real-closed fields transfers it bidirectionally between
;; this representation and the usual real numbers. No rational, finite, or
;; algebraic-only subcarrier replaces the source domain.

(defstub p94b2-member-p (real-type value) t)
(defstub p94b2-zero (real-type) t)
(defstub p94b2-one (real-type) t)
(defstub p94b2-add (real-type left right) t)
(defstub p94b2-multiply (real-type left right) t)
(defstub p94b2-negate (real-type value) t)
(defstub p94b2-inverse (real-type value) t)
(defstub p94b2-less (real-type left right) t)

(defun p94b2-r-add (real-type left right)
  (p94b2-add real-type left right))

(defun p94b2-r-multiply (real-type left right)
  (p94b2-multiply real-type left right))

(defun p94b2-r-negate (real-type value)
  (p94b2-negate real-type value))

(defun p94b2-r-inverse (real-type value)
  (p94b2-inverse real-type value))

(defun p94b2-r-subtract (real-type left right)
  (p94b2-r-add
   real-type left (p94b2-r-negate real-type right)))

(defun p94b2-r-divide (real-type numerator denominator)
  (p94b2-r-multiply
   real-type numerator (p94b2-r-inverse real-type denominator)))

(defun p94b2-leq (real-type left right)
  (not (p94b2-less real-type right left)))

(defun p94b2-square (real-type value)
  (p94b2-r-multiply real-type value value))

(defun p94b2-cube (real-type value)
  (p94b2-r-multiply
   real-type (p94b2-square real-type value) value))

(defun p94b2-fourth-power (real-type value)
  (p94b2-square real-type (p94b2-square real-type value)))

(defun p94b2-r-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p94b2-zero real-type)
    (p94b2-r-add
     real-type
     (p94b2-one real-type)
     (p94b2-r-nat real-type (1- n)))))

(defun-sk p94b2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p94b2-member-p real-type x)
      (p94b2-member-p real-type y)
      (p94b2-member-p real-type z))
     (let* ((zero (p94b2-zero real-type))
            (one (p94b2-one real-type))
            (xy-add (p94b2-r-add real-type x y))
            (yz-add (p94b2-r-add real-type y z))
            (xy-mul (p94b2-r-multiply real-type x y))
            (yz-mul (p94b2-r-multiply real-type y z))
            (neg-x (p94b2-r-negate real-type x))
            (inv-x (p94b2-r-inverse real-type x)))
       (and
        (p94b2-member-p real-type xy-add)
        (p94b2-member-p real-type xy-mul)
        (p94b2-member-p real-type neg-x)
        (p94b2-member-p real-type inv-x)
        (equal
         (p94b2-r-add real-type xy-add z)
         (p94b2-r-add real-type x yz-add))
        (equal xy-add (p94b2-r-add real-type y x))
        (equal (p94b2-r-add real-type x zero) x)
        (equal (p94b2-r-add real-type x neg-x) zero)
        (equal
         (p94b2-r-multiply real-type xy-mul z)
         (p94b2-r-multiply real-type x yz-mul))
        (equal xy-mul (p94b2-r-multiply real-type y x))
        (equal (p94b2-r-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p94b2-r-multiply real-type x inv-x)
          one))
        (equal
         (p94b2-r-multiply real-type x yz-add)
         (p94b2-r-add
          real-type
          (p94b2-r-multiply real-type x y)
          (p94b2-r-multiply real-type x z))))))))

(defun-sk p94b2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p94b2-member-p real-type x)
      (p94b2-member-p real-type y)
      (p94b2-member-p real-type z))
     (let ((zero (p94b2-zero real-type)))
       (and
        (not (p94b2-less real-type x x))
        (or
         (p94b2-less real-type x y)
         (equal x y)
         (p94b2-less real-type y x))
        (implies
         (and
          (p94b2-less real-type x y)
          (p94b2-less real-type y z))
         (p94b2-less real-type x z))
        (implies
         (p94b2-less real-type x y)
         (p94b2-less
          real-type
          (p94b2-r-add real-type x z)
          (p94b2-r-add real-type y z)))
        (implies
         (and
          (p94b2-less real-type zero x)
          (p94b2-less real-type zero y))
         (p94b2-less
          real-type
          zero
          (p94b2-r-multiply real-type x y))))))))

;; A standard first-order characterization of real-closed ordered fields:
;; every nonnegative element is a square, and every odd-degree polynomial has
;; a root. Coefficient lists below are constant-term first.

(defun p94b2-polynomial-p (real-type coefficients)
  (if (consp coefficients)
      (and
       (p94b2-member-p real-type (car coefficients))
       (p94b2-polynomial-p real-type (cdr coefficients)))
    (equal coefficients nil)))

(defun p94b2-leading-coefficient (coefficients)
  (if (consp (cdr coefficients))
      (p94b2-leading-coefficient (cdr coefficients))
    (car coefficients)))

(defun p94b2-polynomial-value
    (real-type coefficients value)
  (if (consp coefficients)
      (p94b2-r-add
       real-type
       (car coefficients)
       (p94b2-r-multiply
        real-type
        value
        (p94b2-polynomial-value
         real-type (cdr coefficients) value)))
    (p94b2-zero real-type)))

(defun p94b2-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (p94b2-polynomial-p real-type coefficients)
   (oddp (1- (len coefficients)))
   (not
    (equal
     (p94b2-leading-coefficient coefficients)
     (p94b2-zero real-type)))))

(defun-sk p94b2-nonnegative-square-root-exists-p
    (real-type value)
  (exists (root)
    (and
     (p94b2-member-p real-type root)
     (equal
      (p94b2-square real-type root)
      value))))

(defun-sk p94b2-nonnegative-elements-are-squares-p
    (real-type)
  (forall (value)
    (implies
     (and
      (p94b2-member-p real-type value)
      (p94b2-leq
       real-type (p94b2-zero real-type) value))
     (p94b2-nonnegative-square-root-exists-p
      real-type value))))

(defun-sk p94b2-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (p94b2-member-p real-type root)
     (equal
      (p94b2-polynomial-value
       real-type coefficients root)
      (p94b2-zero real-type)))))

(defun-sk p94b2-odd-polynomials-have-roots-p
    (real-type)
  (forall (coefficients)
    (implies
     (p94b2-odd-degree-polynomial-p
      real-type coefficients)
     (p94b2-polynomial-root-exists-p
      real-type coefficients))))

(defun p94b2-real-closed-field-p (real-type)
  (let ((zero (p94b2-zero real-type))
        (one (p94b2-one real-type)))
    (and
     (p94b2-member-p real-type zero)
     (p94b2-member-p real-type one)
     (not (equal zero one))
     (p94b2-field-laws-p real-type)
     (p94b2-order-laws-p real-type)
     (p94b2-less real-type zero one)
     (p94b2-nonnegative-elements-are-squares-p real-type)
     (p94b2-odd-polynomials-have-roots-p real-type))))

(defun p94b2-curve-value (real-type c x)
  (let ((nine (p94b2-r-nat real-type 9))
        (four (p94b2-r-nat real-type 4)))
    (p94b2-r-add
     real-type
     (p94b2-fourth-power real-type x)
     (p94b2-r-add
      real-type
      (p94b2-r-multiply
       real-type nine (p94b2-cube real-type x))
      (p94b2-r-add
       real-type
       (p94b2-r-multiply
        real-type c (p94b2-square real-type x))
       (p94b2-r-add
        real-type
        (p94b2-r-multiply real-type nine x)
        four))))))

(defun p94b2-line-value (real-type m b x)
  (p94b2-r-add
   real-type
   (p94b2-r-multiply real-type m x)
   b))

(defun p94b2-intersection-p (real-type c m b x)
  (and
   (p94b2-member-p real-type x)
   (equal
    (p94b2-line-value real-type m b x)
    (p94b2-curve-value real-type c x))))

(defun p94b2-four-distinct-p (x1 x2 x3 x4)
  (and
   (not (equal x1 x2))
   (not (equal x1 x3))
   (not (equal x1 x4))
   (not (equal x2 x3))
   (not (equal x2 x4))
   (not (equal x3 x4))))

(defun-sk p94b2-all-intersections-listed-p
    (real-type c m b x1 x2 x3 x4)
  (forall (x)
    (implies
     (p94b2-intersection-p real-type c m b x)
     (or
      (equal x x1)
      (equal x x2)
      (equal x x3)
      (equal x x4)))))

(defun p94b2-exactly-four-intersections-witness-p
    (real-type c m b x1 x2 x3 x4)
  (and
   (p94b2-member-p real-type m)
   (p94b2-member-p real-type b)
   (p94b2-member-p real-type x1)
   (p94b2-member-p real-type x2)
   (p94b2-member-p real-type x3)
   (p94b2-member-p real-type x4)
   (p94b2-four-distinct-p x1 x2 x3 x4)
   (p94b2-intersection-p real-type c m b x1)
   (p94b2-intersection-p real-type c m b x2)
   (p94b2-intersection-p real-type c m b x3)
   (p94b2-intersection-p real-type c m b x4)
   (p94b2-all-intersections-listed-p
    real-type c m b x1 x2 x3 x4)))

(defun-sk p94b2-line-with-exactly-four-intersections-exists-p
    (real-type c)
  (exists (m b x1 x2 x3 x4)
    (p94b2-exactly-four-intersections-witness-p
     real-type c m b x1 x2 x3 x4)))

(defun p94b2-solution-p (real-type c)
  (p94b2-less
   real-type
   c
   (p94b2-r-divide
    real-type
    (p94b2-r-nat real-type 243)
    (p94b2-r-nat real-type 8))))

(defun putnambench-putnam-1994-b2-statement
    (real-type c)
  (implies
   (and
    (p94b2-real-closed-field-p real-type)
    (p94b2-member-p real-type c))
   (iff
    (p94b2-line-with-exactly-four-intersections-exists-p
     real-type c)
    (p94b2-solution-p real-type c))))

(value-triple :itpeval-statement-checked)
:q
