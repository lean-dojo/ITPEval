;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_b2:
;; for 0 < b < a, the infimum perimeter of nondegenerate triangles with
;; vertices (a,b), (c,0), and (x,x) is sqrt(2*a^2 + 2*b^2). This file contains
;; no proof.

(in-package "ACL2")

;; The conservative interfaces below present an arbitrary real-closed ordered
;; field.  After expanding the displayed infimum into its greatest-lower-bound
;; definition, the source proposition is a closed first-order ordered-field
;; sentence.  Real-closed fields have the same first-order theory as the reals,
;; and the real algebraic numbers give a non-vacuous countable model inside
;; ACL2's value universe.  Thus the full-carrier quantifiers below preserve the
;; arbitrary-real domain without rational probes, finite tables, or an external
;; minimizing witness.

(defstub p98b2-member-p (real-type value) t)
(defstub p98b2-zero (real-type) t)
(defstub p98b2-one (real-type) t)
(defstub p98b2-add (real-type left right) t)
(defstub p98b2-multiply (real-type left right) t)
(defstub p98b2-negate (real-type value) t)
(defstub p98b2-inverse (real-type value) t)
(defstub p98b2-less (real-type left right) t)
(defstub p98b2-square-root (real-type value) t)

(defun p98b2-r-add (real-type left right)
  (p98b2-add real-type left right))

(defun p98b2-r-multiply (real-type left right)
  (p98b2-multiply real-type left right))

(defun p98b2-r-negate (real-type value)
  (p98b2-negate real-type value))

(defun p98b2-r-inverse (real-type value)
  (p98b2-inverse real-type value))

(defun p98b2-r-subtract (real-type left right)
  (p98b2-r-add
   real-type left (p98b2-r-negate real-type right)))

(defun p98b2-leq (real-type left right)
  (not (p98b2-less real-type right left)))

(defun p98b2-square (real-type value)
  (p98b2-r-multiply real-type value value))

(defun p98b2-two (real-type)
  (p98b2-r-add
   real-type
   (p98b2-one real-type)
   (p98b2-one real-type)))

(defun-sk p98b2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p98b2-member-p real-type x)
      (p98b2-member-p real-type y)
      (p98b2-member-p real-type z))
     (let* ((zero (p98b2-zero real-type))
            (one (p98b2-one real-type))
            (xy-add (p98b2-r-add real-type x y))
            (yz-add (p98b2-r-add real-type y z))
            (xy-mul (p98b2-r-multiply real-type x y))
            (yz-mul (p98b2-r-multiply real-type y z))
            (neg-x (p98b2-r-negate real-type x))
            (inv-x (p98b2-r-inverse real-type x)))
       (and
        (p98b2-member-p real-type xy-add)
        (p98b2-member-p real-type xy-mul)
        (p98b2-member-p real-type neg-x)
        (p98b2-member-p real-type inv-x)
        (equal
         (p98b2-r-add real-type xy-add z)
         (p98b2-r-add real-type x yz-add))
        (equal xy-add (p98b2-r-add real-type y x))
        (equal (p98b2-r-add real-type x zero) x)
        (equal (p98b2-r-add real-type x neg-x) zero)
        (equal
         (p98b2-r-multiply real-type xy-mul z)
         (p98b2-r-multiply real-type x yz-mul))
        (equal xy-mul (p98b2-r-multiply real-type y x))
        (equal (p98b2-r-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p98b2-r-multiply real-type x inv-x)
          one))
        (equal
         (p98b2-r-multiply real-type x yz-add)
         (p98b2-r-add
          real-type
          (p98b2-r-multiply real-type x y)
          (p98b2-r-multiply real-type x z))))))))

(defun-sk p98b2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p98b2-member-p real-type x)
      (p98b2-member-p real-type y)
      (p98b2-member-p real-type z))
     (let ((zero (p98b2-zero real-type)))
       (and
        (not (p98b2-less real-type x x))
        (or
         (p98b2-less real-type x y)
         (equal x y)
         (p98b2-less real-type y x))
        (implies
         (and
          (p98b2-less real-type x y)
          (p98b2-less real-type y z))
         (p98b2-less real-type x z))
        (implies
         (p98b2-less real-type x y)
         (p98b2-less
          real-type
          (p98b2-r-add real-type x z)
          (p98b2-r-add real-type y z)))
        (implies
         (and
          (p98b2-less real-type zero x)
          (p98b2-less real-type zero y))
         (p98b2-less
          real-type
          zero
          (p98b2-r-multiply real-type x y))))))))

;; One first-order characterization of real-closed ordered fields: every
;; nonnegative element is a square and every odd-degree polynomial has a root.
;; Coefficient lists are constant-term first.

(defun p98b2-polynomial-p (real-type coefficients)
  (if (consp coefficients)
      (and
       (p98b2-member-p real-type (car coefficients))
       (p98b2-polynomial-p real-type (cdr coefficients)))
    (equal coefficients nil)))

(defun p98b2-leading-coefficient (coefficients)
  (if (consp (cdr coefficients))
      (p98b2-leading-coefficient (cdr coefficients))
    (car coefficients)))

(defun p98b2-polynomial-value
    (real-type coefficients value)
  (if (consp coefficients)
      (p98b2-r-add
       real-type
       (car coefficients)
       (p98b2-r-multiply
        real-type
        value
        (p98b2-polynomial-value
         real-type (cdr coefficients) value)))
    (p98b2-zero real-type)))

(defun p98b2-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (p98b2-polynomial-p real-type coefficients)
   (oddp (1- (len coefficients)))
   (not
    (equal
     (p98b2-leading-coefficient coefficients)
     (p98b2-zero real-type)))))

(defun-sk p98b2-nonnegative-square-root-exists-p
    (real-type value)
  (exists (root)
    (and
     (p98b2-member-p real-type root)
     (equal
      (p98b2-square real-type root)
      value))))

(defun-sk p98b2-positive-elements-are-squares-p
    (real-type)
  (forall (value)
    (implies
     (and
      (p98b2-member-p real-type value)
      (p98b2-leq
       real-type (p98b2-zero real-type) value))
     (p98b2-nonnegative-square-root-exists-p
      real-type value))))

(defun-sk p98b2-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (p98b2-member-p real-type root)
     (equal
      (p98b2-polynomial-value
       real-type coefficients root)
      (p98b2-zero real-type)))))

(defun-sk p98b2-odd-polynomials-have-roots-p
    (real-type)
  (forall (coefficients)
    (implies
     (p98b2-odd-degree-polynomial-p
      real-type coefficients)
     (p98b2-polynomial-root-exists-p
      real-type coefficients))))

;; This fixes the square-root symbol to the source's principal real square
;; root, including its conventional zero value on negative arguments.

(defun-sk p98b2-square-root-laws-p (real-type)
  (forall (value)
    (implies
     (p98b2-member-p real-type value)
     (let ((zero (p98b2-zero real-type))
           (root (p98b2-square-root real-type value)))
       (and
        (p98b2-member-p real-type root)
        (if (p98b2-less real-type value zero)
            (equal root zero)
          (and
           (p98b2-leq real-type zero root)
           (equal
            (p98b2-square real-type root)
            value))))))))

(defun p98b2-real-closed-field-p (real-type)
  (let ((zero (p98b2-zero real-type))
        (one (p98b2-one real-type)))
    (and
     (p98b2-member-p real-type zero)
     (p98b2-member-p real-type one)
     (not (equal zero one))
     (p98b2-field-laws-p real-type)
     (p98b2-order-laws-p real-type)
     (p98b2-less real-type zero one)
     (p98b2-positive-elements-are-squares-p real-type)
     (p98b2-odd-polynomials-have-roots-p real-type)
     (p98b2-square-root-laws-p real-type))))

(defun p98b2-distance
    (real-type left-x left-y right-x right-y)
  (let ((delta-x
         (p98b2-r-subtract real-type left-x right-x))
        (delta-y
         (p98b2-r-subtract real-type left-y right-y)))
    (p98b2-square-root
     real-type
     (p98b2-r-add
      real-type
      (p98b2-square real-type delta-x)
      (p98b2-square real-type delta-y)))))

(defun p98b2-first-side (real-type a b c)
  (p98b2-distance
   real-type
   a b c (p98b2-zero real-type)))

(defun p98b2-second-side (real-type c x)
  (p98b2-distance
   real-type
   c (p98b2-zero real-type) x x))

(defun p98b2-third-side (real-type a b x)
  (p98b2-distance real-type a b x x))

(defun p98b2-perimeter (real-type a b c x)
  (p98b2-r-add
   real-type
   (p98b2-first-side real-type a b c)
   (p98b2-r-add
    real-type
    (p98b2-second-side real-type c x)
    (p98b2-third-side real-type a b x))))

(defun p98b2-admissible-p (real-type a b c x)
  (and
   (p98b2-member-p real-type c)
   (p98b2-member-p real-type x)
   (let ((first (p98b2-first-side real-type a b c))
         (second (p98b2-second-side real-type c x))
         (third (p98b2-third-side real-type a b x)))
     (and
      (p98b2-less
       real-type
       third
       (p98b2-r-add real-type first second))
      (p98b2-less
       real-type
       second
       (p98b2-r-add real-type first third))
      (p98b2-less
       real-type
       first
       (p98b2-r-add real-type second third))))))

(defun p98b2-solution (real-type a b)
  (let ((two (p98b2-two real-type)))
    (p98b2-square-root
     real-type
     (p98b2-r-add
      real-type
      (p98b2-r-multiply
       real-type two (p98b2-square real-type a))
      (p98b2-r-multiply
       real-type two (p98b2-square real-type b))))))

;; These two unbounded quantifiers are the exact greatest-lower-bound
;; definition of the source sInf, not an approximation or an attainment
;; shortcut.

(defun-sk p98b2-lower-bound-p
    (real-type a b bound)
  (forall (c x)
    (implies
     (p98b2-admissible-p real-type a b c x)
     (p98b2-leq
      real-type
      bound
      (p98b2-perimeter real-type a b c x)))))

(defun-sk p98b2-greatest-lower-bound-p
    (real-type a b candidate)
  (forall (bound)
    (implies
     (and
      (p98b2-member-p real-type bound)
      (p98b2-lower-bound-p real-type a b bound))
     (p98b2-leq real-type bound candidate))))

(defun p98b2-is-infimum-p
    (real-type a b candidate)
  (and
   (p98b2-member-p real-type candidate)
   (p98b2-lower-bound-p real-type a b candidate)
   (p98b2-greatest-lower-bound-p
    real-type a b candidate)))

(defun-sk putnambench-putnam-1998-b2-statement
    (real-type)
  (forall (a b)
    (implies
     (and
      (p98b2-real-closed-field-p real-type)
      (p98b2-member-p real-type a)
      (p98b2-member-p real-type b)
      (p98b2-less
       real-type (p98b2-zero real-type) b)
      (p98b2-less real-type b a))
     (p98b2-is-infimum-p
      real-type
      a
      b
      (p98b2-solution real-type a b)))))

(value-triple :itpeval-statement-checked)
:q
