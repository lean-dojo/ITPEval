;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__053, "Pi is Transcendental": the real number pi
;; is not a root of any nonzero integer polynomial. Pi is an actual element
;; of an Archimedean ordered field, fixed by convergence of Machin's series.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces for an unbounded Archimedean ordered field and
;; its distinguished real number pi. Every required field, order, domain,
;; and convergence property is explicit in the statement predicate.

(defstub ht053-real-p (real-type value) t)
(defstub ht053-zero (real-type) t)
(defstub ht053-one (real-type) t)
(defstub ht053-add (real-type left right) t)
(defstub ht053-mul (real-type left right) t)
(defstub ht053-neg (real-type value) t)
(defstub ht053-inv (real-type value) t)
(defstub ht053-less (real-type left right) t)
(defstub ht053-pi (real-type) t)

(defun ht053-leq (real-type left right)
  (not (ht053-less real-type right left)))

(defun ht053-positive-p (real-type value)
  (and
   (ht053-real-p real-type value)
   (ht053-less
    real-type (ht053-zero real-type) value)))

(defun ht053-sub (real-type left right)
  (ht053-add real-type left (ht053-neg real-type right)))

(defun ht053-div (real-type numerator denominator)
  (ht053-mul
   real-type numerator (ht053-inv real-type denominator)))

(defun ht053-abs (real-type value)
  (if (ht053-less real-type value (ht053-zero real-type))
      (ht053-neg real-type value)
    value))

(defun ht053-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (ht053-zero real-type)
    (ht053-add
     real-type
     (ht053-one real-type)
     (ht053-nat real-type (1- n)))))

(defun ht053-integer (real-type integer)
  (if (and (integerp integer) (< integer 0))
      (ht053-neg
       real-type
       (ht053-nat real-type (- integer)))
    (ht053-nat real-type (nfix integer))))

(defun ht053-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ht053-one real-type)
    (ht053-mul
     real-type
     base
     (ht053-power real-type base (1- exponent)))))

(defun-sk ht053-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (ht053-real-p real-type x)
      (ht053-real-p real-type y)
      (ht053-real-p real-type z))
     (let* ((zero (ht053-zero real-type))
            (one (ht053-one real-type))
            (xy-add (ht053-add real-type x y))
            (yz-add (ht053-add real-type y z))
            (xy-mul (ht053-mul real-type x y))
            (yz-mul (ht053-mul real-type y z))
            (neg-x (ht053-neg real-type x))
            (inv-x (ht053-inv real-type x)))
       (and
        (ht053-real-p real-type xy-add)
        (ht053-real-p real-type xy-mul)
        (ht053-real-p real-type neg-x)
        (ht053-real-p real-type inv-x)
        (equal
         (ht053-add real-type xy-add z)
         (ht053-add real-type x yz-add))
        (equal xy-add (ht053-add real-type y x))
        (equal (ht053-add real-type x zero) x)
        (equal (ht053-add real-type x neg-x) zero)
        (equal
         (ht053-mul real-type xy-mul z)
         (ht053-mul real-type x yz-mul))
        (equal xy-mul (ht053-mul real-type y x))
        (equal (ht053-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (ht053-mul real-type x inv-x) one))
        (equal
         (ht053-mul real-type x yz-add)
         (ht053-add
          real-type
          (ht053-mul real-type x y)
          (ht053-mul real-type x z))))))))

(defun-sk ht053-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (ht053-real-p real-type x)
      (ht053-real-p real-type y)
      (ht053-real-p real-type z))
     (let ((zero (ht053-zero real-type)))
       (and
        (not (ht053-less real-type x x))
        (or
         (ht053-less real-type x y)
         (equal x y)
         (ht053-less real-type y x))
        (implies
         (and
          (ht053-less real-type x y)
          (ht053-less real-type y z))
         (ht053-less real-type x z))
        (implies
         (ht053-less real-type x y)
         (ht053-less
          real-type
          (ht053-add real-type x z)
          (ht053-add real-type y z)))
        (implies
         (and
          (ht053-less real-type zero x)
          (ht053-less real-type zero y))
         (ht053-less
          real-type
          zero
          (ht053-mul real-type x y))))))))

(defun-sk ht053-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (ht053-less
      real-type value (ht053-nat real-type n)))))

(defun-sk ht053-archimedean-p (real-type)
  (forall (value)
    (implies
     (ht053-real-p real-type value)
     (ht053-archimedean-bound-exists-p
      real-type value))))

(defun ht053-real-field-p (real-type)
  (let ((zero (ht053-zero real-type))
        (one (ht053-one real-type)))
    (and
     (ht053-real-p real-type zero)
     (ht053-real-p real-type one)
     (not (equal zero one))
     (ht053-field-laws-p real-type)
     (ht053-order-laws-p real-type)
     (ht053-less real-type zero one)
     (ht053-archimedean-p real-type))))

;; Machin's identity fixes pi independently of the transcendence conclusion:
;; pi = 16*arctan(1/5) - 4*arctan(1/239).

(defun ht053-arctan-prefix (real-type z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (ht053-zero real-type)
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned
            (ht053-div
             real-type
             (ht053-power real-type z exponent)
             (ht053-nat real-type exponent)))
           (term
            (if (equal (mod index 2) 0)
                unsigned
              (ht053-neg real-type unsigned))))
      (ht053-add
       real-type
       (ht053-arctan-prefix real-type z index)
       term))))

(defun ht053-pi-prefix (real-type terms)
  (let* ((one (ht053-one real-type))
         (five (ht053-nat real-type 5))
         (two-hundred-thirty-nine
          (ht053-nat real-type 239))
         (sixteen (ht053-nat real-type 16))
         (four (ht053-nat real-type 4)))
    (ht053-sub
     real-type
     (ht053-mul
      real-type
      sixteen
      (ht053-arctan-prefix
       real-type
       (ht053-div real-type one five)
       terms))
     (ht053-mul
      real-type
      four
      (ht053-arctan-prefix
       real-type
       (ht053-div
        real-type one two-hundred-thirty-nine)
       terms)))))

(defun-sk ht053-pi-tail-p
    (real-type epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (ht053-less
      real-type
      (ht053-abs
       real-type
       (ht053-sub
        real-type
        (ht053-pi-prefix real-type terms)
        (ht053-pi real-type)))
      epsilon))))

(defun-sk ht053-pi-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht053-pi-tail-p
      real-type epsilon cutoff))))

(defun-sk ht053-pi-converges-p (real-type)
  (forall (epsilon)
    (implies
     (ht053-positive-p real-type epsilon)
     (ht053-pi-cutoff-exists-p
      real-type epsilon))))

(defun ht053-pi-value-p (real-type)
  (and
   (ht053-real-p real-type (ht053-pi real-type))
   (ht053-pi-converges-p real-type)))

(defun ht053-integer-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (integerp (car coefficients))
       (ht053-integer-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun ht053-nonzero-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (or
       (not (equal (car coefficients) 0))
       (ht053-nonzero-coefficient-list-p
        (cdr coefficients)))
    nil))

;; Coefficients are listed in ascending order of exponent. This evaluates
;; the corresponding integer polynomial directly at a field element.

(defun ht053-polynomial-value
    (real-type coefficients x)
  (if (consp coefficients)
      (ht053-add
       real-type
       (ht053-integer real-type (car coefficients))
       (ht053-mul
        real-type
        x
        (ht053-polynomial-value
         real-type (cdr coefficients) x)))
    (ht053-zero real-type)))

(defun-sk ht053-pi-transcendental-p (real-type)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (ht053-integer-coefficient-list-p coefficients)
      (ht053-nonzero-coefficient-list-p coefficients))
     (not
      (equal
       (ht053-polynomial-value
        real-type
        coefficients
        (ht053-pi real-type))
       (ht053-zero real-type))))))

(defun hundred-theorems-053-pi-is-transcendental-statement
    (real-type)
  (implies
   (and
    (ht053-real-field-p real-type)
    (ht053-pi-value-p real-type))
   (ht053-pi-transcendental-p real-type)))

(value-triple :itpeval-statement-checked)
:q
