;; Statement-only formalization of PutnamBench corpus artifact putnam_1967_a1:
;; a real sine polynomial bounded in absolute value by |sin(x)| has its
;; weighted coefficient sum bounded in absolute value by one. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative interfaces present a Dedekind-complete ordered field,
;; hence the real field up to ordered-field isomorphism. Coefficients are
;; values of an arbitrary function token; they are not restricted to
;; rationals, algebraic reals, a finite carrier, or a finite lookup table.

(defstub putnam-1967-a1-real-p (real-type value) t)
(defstub putnam-1967-a1-zero (real-type) t)
(defstub putnam-1967-a1-one (real-type) t)
(defstub putnam-1967-a1-add (real-type left right) t)
(defstub putnam-1967-a1-mul (real-type left right) t)
(defstub putnam-1967-a1-neg (real-type value) t)
(defstub putnam-1967-a1-inv (real-type value) t)
(defstub putnam-1967-a1-lt (real-type left right) t)
(defstub putnam-1967-a1-set-member-p (real-type set value) t)
(defstub putnam-1967-a1-coefficient
  (real-type coefficients index) t)

(defun putnam-1967-a1-sub (real-type left right)
  (putnam-1967-a1-add
   real-type left (putnam-1967-a1-neg real-type right)))

(defun putnam-1967-a1-le (real-type left right)
  (not (putnam-1967-a1-lt real-type right left)))

(defun putnam-1967-a1-abs (real-type value)
  (if (putnam-1967-a1-lt
       real-type value (putnam-1967-a1-zero real-type))
      (putnam-1967-a1-neg real-type value)
    value))

(defun putnam-1967-a1-real-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1967-a1-zero real-type)
    (putnam-1967-a1-add
     real-type
     (putnam-1967-a1-one real-type)
     (putnam-1967-a1-real-nat real-type (1- n)))))

;; A complete ordered-field presentation of the real carrier.

(defun-sk putnam-1967-a1-operation-closure-p (real-type)
  (forall (x y)
    (and
     (putnam-1967-a1-real-p
      real-type (putnam-1967-a1-zero real-type))
     (putnam-1967-a1-real-p
      real-type (putnam-1967-a1-one real-type))
     (implies
      (putnam-1967-a1-real-p real-type x)
      (and
       (putnam-1967-a1-real-p
        real-type (putnam-1967-a1-neg real-type x))
       (putnam-1967-a1-real-p
        real-type (putnam-1967-a1-inv real-type x))))
     (implies
      (and
       (putnam-1967-a1-real-p real-type x)
       (putnam-1967-a1-real-p real-type y))
      (and
       (putnam-1967-a1-real-p
        real-type (putnam-1967-a1-add real-type x y))
       (putnam-1967-a1-real-p
        real-type (putnam-1967-a1-mul real-type x y)))))))

(defun-sk putnam-1967-a1-unary-field-laws-p (real-type)
  (forall (x)
    (implies
     (putnam-1967-a1-real-p real-type x)
     (let ((zero (putnam-1967-a1-zero real-type))
           (one (putnam-1967-a1-one real-type)))
       (and
        (equal (putnam-1967-a1-add real-type zero x) x)
        (equal (putnam-1967-a1-add real-type x zero) x)
        (equal
         (putnam-1967-a1-add
          real-type x (putnam-1967-a1-neg real-type x))
         zero)
        (equal (putnam-1967-a1-mul real-type one x) x)
        (equal (putnam-1967-a1-mul real-type x one) x)
        (implies
         (not (equal x zero))
         (equal
          (putnam-1967-a1-mul
           real-type x (putnam-1967-a1-inv real-type x))
          one)))))))

(defun-sk putnam-1967-a1-binary-field-laws-p (real-type)
  (forall (x y)
    (implies
     (and
      (putnam-1967-a1-real-p real-type x)
      (putnam-1967-a1-real-p real-type y))
     (and
      (equal
       (putnam-1967-a1-add real-type x y)
       (putnam-1967-a1-add real-type y x))
      (equal
       (putnam-1967-a1-mul real-type x y)
       (putnam-1967-a1-mul real-type y x))))))

(defun-sk putnam-1967-a1-ternary-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1967-a1-real-p real-type x)
      (putnam-1967-a1-real-p real-type y)
      (putnam-1967-a1-real-p real-type z))
     (and
      (equal
       (putnam-1967-a1-add
        real-type (putnam-1967-a1-add real-type x y) z)
       (putnam-1967-a1-add
        real-type x (putnam-1967-a1-add real-type y z)))
      (equal
       (putnam-1967-a1-mul
        real-type (putnam-1967-a1-mul real-type x y) z)
       (putnam-1967-a1-mul
        real-type x (putnam-1967-a1-mul real-type y z)))
      (equal
       (putnam-1967-a1-mul
        real-type x (putnam-1967-a1-add real-type y z))
       (putnam-1967-a1-add
        real-type
        (putnam-1967-a1-mul real-type x y)
        (putnam-1967-a1-mul real-type x z)))))))

(defun-sk putnam-1967-a1-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1967-a1-real-p real-type x)
      (putnam-1967-a1-real-p real-type y)
      (putnam-1967-a1-real-p real-type z))
     (and
      (not (putnam-1967-a1-lt real-type x x))
      (or
       (putnam-1967-a1-lt real-type x y)
       (equal x y)
       (putnam-1967-a1-lt real-type y x))
      (implies
       (and
        (putnam-1967-a1-lt real-type x y)
        (putnam-1967-a1-lt real-type y z))
       (putnam-1967-a1-lt real-type x z))
      (implies
       (putnam-1967-a1-lt real-type x y)
       (putnam-1967-a1-lt
        real-type
        (putnam-1967-a1-add real-type x z)
        (putnam-1967-a1-add real-type y z)))
      (implies
       (and
        (putnam-1967-a1-lt
         real-type (putnam-1967-a1-zero real-type) x)
        (putnam-1967-a1-lt
         real-type (putnam-1967-a1-zero real-type) y))
       (putnam-1967-a1-lt
        real-type
        (putnam-1967-a1-zero real-type)
        (putnam-1967-a1-mul real-type x y)))))))

(defun-sk putnam-1967-a1-valid-real-set-p (real-type set)
  (forall (x)
    (implies
     (putnam-1967-a1-set-member-p real-type set x)
     (putnam-1967-a1-real-p real-type x))))

(defun-sk putnam-1967-a1-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (putnam-1967-a1-real-p real-type x)
     (putnam-1967-a1-set-member-p real-type set x))))

(defun-sk putnam-1967-a1-upper-bound-p
    (real-type set bound)
  (forall (x)
    (implies
     (putnam-1967-a1-set-member-p real-type set x)
     (putnam-1967-a1-le real-type x bound))))

(defun-sk putnam-1967-a1-bounded-above-p (real-type set)
  (exists (bound)
    (and
     (putnam-1967-a1-real-p real-type bound)
     (putnam-1967-a1-upper-bound-p real-type set bound))))

(defun-sk putnam-1967-a1-least-upper-bound-p
    (real-type set supremum)
  (forall (bound)
    (and
     (putnam-1967-a1-real-p real-type supremum)
     (putnam-1967-a1-upper-bound-p real-type set supremum)
     (implies
      (and
       (putnam-1967-a1-real-p real-type bound)
       (putnam-1967-a1-upper-bound-p real-type set bound))
      (putnam-1967-a1-le real-type supremum bound)))))

(defun-sk putnam-1967-a1-supremum-exists-p (real-type set)
  (exists (supremum)
    (and
     (putnam-1967-a1-real-p real-type supremum)
     (putnam-1967-a1-least-upper-bound-p
      real-type set supremum))))

(defun-sk putnam-1967-a1-dedekind-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (putnam-1967-a1-valid-real-set-p real-type set)
      (putnam-1967-a1-set-nonempty-p real-type set)
      (putnam-1967-a1-bounded-above-p real-type set))
     (putnam-1967-a1-supremum-exists-p real-type set))))

(defun putnam-1967-a1-real-structure-p (real-type)
  (and
   (putnam-1967-a1-operation-closure-p real-type)
   (putnam-1967-a1-unary-field-laws-p real-type)
   (putnam-1967-a1-binary-field-laws-p real-type)
   (putnam-1967-a1-ternary-field-laws-p real-type)
   (putnam-1967-a1-order-laws-p real-type)
   (not
    (equal
     (putnam-1967-a1-zero real-type)
     (putnam-1967-a1-one real-type)))
   (putnam-1967-a1-lt
    real-type
    (putnam-1967-a1-zero real-type)
    (putnam-1967-a1-one real-type))
   (putnam-1967-a1-dedekind-complete-p real-type)))

(defun-sk putnam-1967-a1-coefficients-p
    (real-type coefficients n)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= 1 index)
      (<= index n))
     (putnam-1967-a1-real-p
      real-type
      (putnam-1967-a1-coefficient
       real-type coefficients index)))))

;; sin(i*x) = sin(x) U_(i-1)(cos(x)). Thus, after substituting the
;; definition of f, the source hypothesis is equivalent to
;; |sum_i a_i U_(i-1)(t)| <= 1 for every -1 < t < 1. At sin(x)=0 the source
;; inequality is automatic, and every t in (-1,1) is cos(x) for an x with
;; sin(x) nonzero. The conclusion is evaluation at t=1 because U_(i-1)(1)=i.

(defun putnam-1967-a1-chebyshev-u-iter
    (real-type t-value remaining previous current)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      previous
    (putnam-1967-a1-chebyshev-u-iter
     real-type
     t-value
     (1- remaining)
     current
     (putnam-1967-a1-sub
      real-type
      (putnam-1967-a1-mul
       real-type
       (putnam-1967-a1-mul
        real-type
        (putnam-1967-a1-real-nat real-type 2)
        t-value)
       current)
      previous))))

(defun putnam-1967-a1-chebyshev-u
    (real-type index t-value)
  (putnam-1967-a1-chebyshev-u-iter
   real-type
   t-value
   index
   (putnam-1967-a1-one real-type)
   (putnam-1967-a1-mul
    real-type
    (putnam-1967-a1-real-nat real-type 2)
    t-value)))

(defun putnam-1967-a1-polynomial-aux
    (real-type coefficients remaining index t-value)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-1967-a1-zero real-type)
    (putnam-1967-a1-add
     real-type
     (putnam-1967-a1-mul
      real-type
      (putnam-1967-a1-coefficient
       real-type coefficients index)
      (putnam-1967-a1-chebyshev-u
       real-type (1- index) t-value))
     (putnam-1967-a1-polynomial-aux
      real-type coefficients (1- remaining) (1+ index) t-value))))

(defun putnam-1967-a1-polynomial
    (real-type coefficients n t-value)
  (putnam-1967-a1-polynomial-aux
   real-type coefficients n 1 t-value))

(defun-sk putnam-1967-a1-bounded-on-open-unit-p
    (real-type coefficients n)
  (forall (t-value)
    (implies
     (and
      (putnam-1967-a1-real-p real-type t-value)
      (putnam-1967-a1-lt
       real-type
       (putnam-1967-a1-neg
        real-type (putnam-1967-a1-one real-type))
       t-value)
      (putnam-1967-a1-lt
       real-type t-value (putnam-1967-a1-one real-type)))
     (putnam-1967-a1-le
      real-type
      (putnam-1967-a1-abs
       real-type
       (putnam-1967-a1-polynomial
        real-type coefficients n t-value))
      (putnam-1967-a1-one real-type)))))

(defun putnam-1967-a1-weighted-sum-aux
    (real-type coefficients remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-1967-a1-zero real-type)
    (putnam-1967-a1-add
     real-type
     (putnam-1967-a1-mul
      real-type
      (putnam-1967-a1-real-nat real-type index)
      (putnam-1967-a1-coefficient
       real-type coefficients index))
     (putnam-1967-a1-weighted-sum-aux
      real-type coefficients (1- remaining) (1+ index)))))

(defun putnam-1967-a1-weighted-sum
    (real-type coefficients n)
  (putnam-1967-a1-weighted-sum-aux
   real-type coefficients n 1))

(defun-sk putnambench-putnam-1967-a1-statement ()
  (forall (real-type n coefficients)
    (implies
     (and
      (putnam-1967-a1-real-structure-p real-type)
      (natp n)
      (< 0 n)
      (putnam-1967-a1-coefficients-p
       real-type coefficients n)
      (putnam-1967-a1-bounded-on-open-unit-p
       real-type coefficients n))
     (putnam-1967-a1-le
      real-type
      (putnam-1967-a1-abs
       real-type
       (putnam-1967-a1-weighted-sum
        real-type coefficients n))
      (putnam-1967-a1-one real-type)))))

(value-triple :itpeval-statement-checked)
:q
