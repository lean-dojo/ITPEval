;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_b2:
;; the minimum of a four-term sum of squared successive ratios over real
;; numbers 1 <= r <= s <= t <= 4 is 12 - 8*sqrt(2). This file contains no
;; proof.

(in-package "ACL2")

;; These conservative interfaces present scalar operations on an arbitrary
;; carrier.  The statement predicate below explicitly requires that carrier
;; to be a real-closed ordered field and that SQRT-TWO denote its positive
;; square root of two.  Real-closed fields have the same first-order ordered
;; field theory as the reals, so this preserves the source quantification over
;; all real r, s, and t; no rational or finite subcarrier is used.

(defstub p81b2-member-p (real-type value) t)
(defstub p81b2-zero (real-type) t)
(defstub p81b2-one (real-type) t)
(defstub p81b2-add (real-type left right) t)
(defstub p81b2-multiply (real-type left right) t)
(defstub p81b2-negate (real-type value) t)
(defstub p81b2-inverse (real-type value) t)
(defstub p81b2-less (real-type left right) t)
(defstub p81b2-sqrt-two (real-type) t)

(defun p81b2-r-add (real-type left right)
  (p81b2-add real-type left right))

(defun p81b2-r-multiply (real-type left right)
  (p81b2-multiply real-type left right))

(defun p81b2-r-negate (real-type value)
  (p81b2-negate real-type value))

(defun p81b2-r-inverse (real-type value)
  (p81b2-inverse real-type value))

(defun p81b2-r-subtract (real-type left right)
  (p81b2-r-add
   real-type left (p81b2-r-negate real-type right)))

(defun p81b2-r-divide (real-type numerator denominator)
  (p81b2-r-multiply
   real-type numerator (p81b2-r-inverse real-type denominator)))

(defun p81b2-leq (real-type left right)
  (not (p81b2-less real-type right left)))

(defun p81b2-square (real-type value)
  (p81b2-r-multiply real-type value value))

(defun p81b2-two (real-type)
  (p81b2-r-add
   real-type
   (p81b2-one real-type)
   (p81b2-one real-type)))

(defun p81b2-four (real-type)
  (let ((two (p81b2-two real-type)))
    (p81b2-r-add real-type two two)))

(defun p81b2-eight (real-type)
  (let ((four (p81b2-four real-type)))
    (p81b2-r-add real-type four four)))

(defun p81b2-twelve (real-type)
  (p81b2-r-add
   real-type
   (p81b2-eight real-type)
   (p81b2-four real-type)))

(defun-sk p81b2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p81b2-member-p real-type x)
      (p81b2-member-p real-type y)
      (p81b2-member-p real-type z))
     (let* ((zero (p81b2-zero real-type))
            (one (p81b2-one real-type))
            (xy-add (p81b2-r-add real-type x y))
            (yz-add (p81b2-r-add real-type y z))
            (xy-mul (p81b2-r-multiply real-type x y))
            (yz-mul (p81b2-r-multiply real-type y z))
            (neg-x (p81b2-r-negate real-type x))
            (inv-x (p81b2-r-inverse real-type x)))
       (and
        (p81b2-member-p real-type xy-add)
        (p81b2-member-p real-type xy-mul)
        (p81b2-member-p real-type neg-x)
        (p81b2-member-p real-type inv-x)
        (equal
         (p81b2-r-add real-type xy-add z)
         (p81b2-r-add real-type x yz-add))
        (equal xy-add (p81b2-r-add real-type y x))
        (equal (p81b2-r-add real-type x zero) x)
        (equal (p81b2-r-add real-type x neg-x) zero)
        (equal
         (p81b2-r-multiply real-type xy-mul z)
         (p81b2-r-multiply real-type x yz-mul))
        (equal xy-mul (p81b2-r-multiply real-type y x))
        (equal (p81b2-r-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p81b2-r-multiply real-type x inv-x)
          one))
        (equal
         (p81b2-r-multiply real-type x yz-add)
         (p81b2-r-add
          real-type
          (p81b2-r-multiply real-type x y)
          (p81b2-r-multiply real-type x z))))))))

(defun-sk p81b2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p81b2-member-p real-type x)
      (p81b2-member-p real-type y)
      (p81b2-member-p real-type z))
     (let ((zero (p81b2-zero real-type)))
       (and
        (not (p81b2-less real-type x x))
        (or
         (p81b2-less real-type x y)
         (equal x y)
         (p81b2-less real-type y x))
        (implies
         (and
          (p81b2-less real-type x y)
          (p81b2-less real-type y z))
         (p81b2-less real-type x z))
        (implies
         (p81b2-less real-type x y)
         (p81b2-less
          real-type
          (p81b2-r-add real-type x z)
          (p81b2-r-add real-type y z)))
        (implies
         (and
          (p81b2-less real-type zero x)
          (p81b2-less real-type zero y))
         (p81b2-less
          real-type
          zero
          (p81b2-r-multiply real-type x y))))))))

;; One standard first-order characterization of real-closed ordered fields:
;; every nonnegative element is a square and every odd-degree polynomial has
;; a root.  Coefficient lists are constant-term first.

(defun p81b2-polynomial-p (real-type coefficients)
  (if (consp coefficients)
      (and
       (p81b2-member-p real-type (car coefficients))
       (p81b2-polynomial-p real-type (cdr coefficients)))
    (equal coefficients nil)))

(defun p81b2-leading-coefficient (coefficients)
  (if (consp (cdr coefficients))
      (p81b2-leading-coefficient (cdr coefficients))
    (car coefficients)))

(defun p81b2-polynomial-value
    (real-type coefficients value)
  (if (consp coefficients)
      (p81b2-r-add
       real-type
       (car coefficients)
       (p81b2-r-multiply
        real-type
        value
        (p81b2-polynomial-value
         real-type (cdr coefficients) value)))
    (p81b2-zero real-type)))

(defun p81b2-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (p81b2-polynomial-p real-type coefficients)
   (oddp (1- (len coefficients)))
   (not
    (equal
     (p81b2-leading-coefficient coefficients)
     (p81b2-zero real-type)))))

(defun-sk p81b2-nonnegative-square-root-exists-p
    (real-type value)
  (exists (root)
    (and
     (p81b2-member-p real-type root)
     (equal
      (p81b2-square real-type root)
      value))))

(defun-sk p81b2-positive-elements-are-squares-p
    (real-type)
  (forall (value)
    (implies
     (and
      (p81b2-member-p real-type value)
      (p81b2-leq
       real-type (p81b2-zero real-type) value))
     (p81b2-nonnegative-square-root-exists-p
      real-type value))))

(defun-sk p81b2-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (p81b2-member-p real-type root)
     (equal
      (p81b2-polynomial-value
       real-type coefficients root)
      (p81b2-zero real-type)))))

(defun-sk p81b2-odd-polynomials-have-roots-p
    (real-type)
  (forall (coefficients)
    (implies
     (p81b2-odd-degree-polynomial-p
      real-type coefficients)
     (p81b2-polynomial-root-exists-p
      real-type coefficients))))

(defun p81b2-real-closed-field-p (real-type)
  (let ((zero (p81b2-zero real-type))
        (one (p81b2-one real-type))
        (sqrt-two (p81b2-sqrt-two real-type)))
    (and
     (p81b2-member-p real-type zero)
     (p81b2-member-p real-type one)
     (not (equal zero one))
     (p81b2-field-laws-p real-type)
     (p81b2-order-laws-p real-type)
     (p81b2-less real-type zero one)
     (p81b2-positive-elements-are-squares-p real-type)
     (p81b2-odd-polynomials-have-roots-p real-type)
     (p81b2-member-p real-type sqrt-two)
     (p81b2-less real-type zero sqrt-two)
     (equal
      (p81b2-square real-type sqrt-two)
      (p81b2-two real-type)))))

(defun p81b2-objective (real-type r s top)
  (let* ((one (p81b2-one real-type))
         (four (p81b2-four real-type))
         (r-term
          (p81b2-square
           real-type
           (p81b2-r-subtract real-type r one)))
         (s-term
          (p81b2-square
           real-type
           (p81b2-r-subtract
            real-type
            (p81b2-r-divide real-type s r)
            one)))
         (t-term
          (p81b2-square
           real-type
           (p81b2-r-subtract
            real-type
            (p81b2-r-divide real-type top s)
            one)))
         (four-term
          (p81b2-square
           real-type
           (p81b2-r-subtract
            real-type
            (p81b2-r-divide real-type four top)
            one))))
    (p81b2-r-add
     real-type
     (p81b2-r-add real-type r-term s-term)
     (p81b2-r-add real-type t-term four-term))))

(defun p81b2-feasible-p (real-type r s top)
  (let ((one (p81b2-one real-type))
        (four (p81b2-four real-type)))
    (and
     (p81b2-member-p real-type r)
     (p81b2-member-p real-type s)
     (p81b2-member-p real-type top)
     (p81b2-leq real-type one r)
     (p81b2-leq real-type r s)
     (p81b2-leq real-type s top)
     (p81b2-leq real-type top four))))

(defun p81b2-solution (real-type)
  (p81b2-r-subtract
   real-type
   (p81b2-twelve real-type)
   (p81b2-r-multiply
    real-type
    (p81b2-eight real-type)
    (p81b2-sqrt-two real-type))))

(defun-sk p81b2-lower-bound-p (real-type)
  (forall (r s top)
    (implies
     (p81b2-feasible-p real-type r s top)
     (p81b2-leq
      real-type
      (p81b2-solution real-type)
      (p81b2-objective real-type r s top)))))

(defun-sk p81b2-attained-p (real-type)
  (exists (r s top)
    (and
     (p81b2-feasible-p real-type r s top)
     (equal
      (p81b2-objective real-type r s top)
      (p81b2-solution real-type)))))

(defun putnambench-putnam-1981-b2-statement (real-type)
  (implies
   (p81b2-real-closed-field-p real-type)
   (and
    (p81b2-lower-bound-p real-type)
    (p81b2-attained-p real-type))))

(value-triple :itpeval-statement-checked)
:q
