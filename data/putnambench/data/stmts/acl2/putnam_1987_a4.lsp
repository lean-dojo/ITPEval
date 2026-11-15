;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_a4:
;; an arbitrary real-coefficient polynomial satisfying a universal homogeneity
;; and difference identity determines the distance from A to C for arbitrary
;; complex zeros A, B, and C with |B-A| = 10. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; DEFSTUB introduces conservative generic symbols rather than executable
;; surrogates. Their explicit laws below present an arbitrary real closed
;; ordered field, and P is an arbitrary finite list of trivariate monomials.
;; Such lists represent exactly the finite-support real polynomials. Complex
;; numbers are definitionally pairs of field elements. The identity itself
;; gives F(s,t) = P(0,s,t) by taking x = 0 and u = 1, so eliminating F yields
;; a pure first-order field assertion. Real closed fields are elementarily
;; equivalent, making this presentation bidirectionally equivalent to the
;; source assertion over R and C while retaining F and its full quantifier.

(defstub putnam-1987-a4-real-p (x) t)
(defstub putnam-1987-a4-add (x y) t)
(defstub putnam-1987-a4-multiply (x y) t)
(defstub putnam-1987-a4-negate (x) t)
(defstub putnam-1987-a4-inverse (x) t)
(defstub putnam-1987-a4-less (x y) t)
(defstub putnam-1987-a4-square-root (x) t)
(defstub putnam-1987-a4-f (x y) t)

(defun putnam-1987-a4-subtract (x y)
  (putnam-1987-a4-add
   x
   (putnam-1987-a4-negate y)))

(defun putnam-1987-a4-field-natural (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1987-a4-add
     one
     (putnam-1987-a4-field-natural
      (- n 1) zero one))))

(defun putnam-1987-a4-field-rational
    (numerator denominator zero one)
  (putnam-1987-a4-multiply
   (putnam-1987-a4-field-natural
    numerator zero one)
   (putnam-1987-a4-inverse
    (putnam-1987-a4-field-natural
     denominator zero one))))

(defun-sk putnam-1987-a4-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1987-a4-real-p x)
      (putnam-1987-a4-real-p y)
      (putnam-1987-a4-real-p z))
     (and
      (putnam-1987-a4-real-p
       (putnam-1987-a4-add x y))
      (putnam-1987-a4-real-p
       (putnam-1987-a4-multiply x y))
      (putnam-1987-a4-real-p
       (putnam-1987-a4-negate x))
      (putnam-1987-a4-real-p
       (putnam-1987-a4-inverse x))
      (equal
       (putnam-1987-a4-add
        (putnam-1987-a4-add x y)
        z)
       (putnam-1987-a4-add
        x
        (putnam-1987-a4-add y z)))
      (equal
       (putnam-1987-a4-multiply
        (putnam-1987-a4-multiply x y)
        z)
       (putnam-1987-a4-multiply
        x
        (putnam-1987-a4-multiply y z)))
      (equal
       (putnam-1987-a4-add x y)
       (putnam-1987-a4-add y x))
      (equal
       (putnam-1987-a4-multiply x y)
       (putnam-1987-a4-multiply y x))
      (equal
       (putnam-1987-a4-add x zero)
       x)
      (equal
       (putnam-1987-a4-add
        x
        (putnam-1987-a4-negate x))
       zero)
      (equal
       (putnam-1987-a4-multiply x one)
       x)
      (implies
       (equal x zero)
       (equal
        (putnam-1987-a4-inverse x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (putnam-1987-a4-multiply
         x
         (putnam-1987-a4-inverse x))
        one))
      (equal
       (putnam-1987-a4-multiply
        x
        (putnam-1987-a4-add y z))
       (putnam-1987-a4-add
        (putnam-1987-a4-multiply x y)
        (putnam-1987-a4-multiply x z)))))))

(defun-sk putnam-1987-a4-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (putnam-1987-a4-real-p x)
      (putnam-1987-a4-real-p y)
      (putnam-1987-a4-real-p z))
     (and
      (not (putnam-1987-a4-less x x))
      (or
       (putnam-1987-a4-less x y)
       (equal x y)
       (putnam-1987-a4-less y x))
      (implies
       (and
        (putnam-1987-a4-less x y)
        (putnam-1987-a4-less y z))
       (putnam-1987-a4-less x z))
      (implies
       (putnam-1987-a4-less x y)
       (putnam-1987-a4-less
        (putnam-1987-a4-add x z)
        (putnam-1987-a4-add y z)))
      (implies
       (and
        (putnam-1987-a4-less zero x)
        (putnam-1987-a4-less zero y))
       (putnam-1987-a4-less
        zero
        (putnam-1987-a4-multiply x y)))))))

(defun-sk putnam-1987-a4-square-root-laws-p (zero)
  (forall (x)
    (implies
     (and
      (putnam-1987-a4-real-p x)
      (not (putnam-1987-a4-less x zero)))
     (let ((root
            (putnam-1987-a4-square-root x)))
       (and
        (putnam-1987-a4-real-p root)
        (not (putnam-1987-a4-less root zero))
        (equal
         (putnam-1987-a4-multiply root root)
         x))))))

(defun putnam-1987-a4-real-list-p (values)
  (if (consp values)
      (and
       (putnam-1987-a4-real-p (car values))
       (putnam-1987-a4-real-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1987-a4-univariate-polynomial-p
    (coefficients zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-1987-a4-real-list-p coefficients)
   (or
    (equal (len coefficients) 1)
    (not
     (equal
      (car (last coefficients))
      zero)))))

(defun putnam-1987-a4-univariate-eval
    (coefficients x zero)
  (if (consp coefficients)
      (putnam-1987-a4-add
       (car coefficients)
       (putnam-1987-a4-multiply
        x
        (putnam-1987-a4-univariate-eval
         (cdr coefficients) x zero)))
    zero))

(defun-sk putnam-1987-a4-odd-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (putnam-1987-a4-real-p root)
     (equal
      (putnam-1987-a4-univariate-eval
       coefficients root zero)
      zero))))

(defun-sk putnam-1987-a4-odd-root-laws-p (zero)
  (forall (coefficients)
    (implies
     (and
      (putnam-1987-a4-univariate-polynomial-p
       coefficients zero)
      (evenp (len coefficients)))
     (putnam-1987-a4-odd-root-exists-p
      coefficients zero))))

(defun putnam-1987-a4-real-closed-field-p (zero one)
  (and
   (putnam-1987-a4-real-p zero)
   (putnam-1987-a4-real-p one)
   (not (equal zero one))
   (putnam-1987-a4-field-laws-p zero one)
   (putnam-1987-a4-order-laws-p zero)
   (putnam-1987-a4-square-root-laws-p zero)
   (putnam-1987-a4-odd-root-laws-p zero)))

(defun-sk putnam-1987-a4-f-real-valued-p ()
  (forall (x y)
    (implies
     (and
      (putnam-1987-a4-real-p x)
      (putnam-1987-a4-real-p y))
     (putnam-1987-a4-real-p
      (putnam-1987-a4-f x y)))))

;; A monomial is (coefficient x-exponent y-exponent z-exponent).

(defun putnam-1987-a4-monomial-p (monomial)
  (and
   (true-listp monomial)
   (equal (len monomial) 4)
   (putnam-1987-a4-real-p (nth 0 monomial))
   (natp (nth 1 monomial))
   (natp (nth 2 monomial))
   (natp (nth 3 monomial))))

(defun putnam-1987-a4-polynomial-p (polynomial)
  (if (consp polynomial)
      (and
       (putnam-1987-a4-monomial-p
        (car polynomial))
       (putnam-1987-a4-polynomial-p
        (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1987-a4-power (x n one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (putnam-1987-a4-multiply
     x
     (putnam-1987-a4-power
      x (- n 1) one))))

(defun putnam-1987-a4-monomial-real-eval
    (monomial x y z one)
  (putnam-1987-a4-multiply
   (nth 0 monomial)
   (putnam-1987-a4-multiply
    (putnam-1987-a4-power
     x (nth 1 monomial) one)
    (putnam-1987-a4-multiply
     (putnam-1987-a4-power
      y (nth 2 monomial) one)
     (putnam-1987-a4-power
      z (nth 3 monomial) one)))))

(defun putnam-1987-a4-polynomial-real-eval
    (polynomial x y z zero one)
  (if (consp polynomial)
      (putnam-1987-a4-add
       (putnam-1987-a4-monomial-real-eval
        (car polynomial) x y z one)
       (putnam-1987-a4-polynomial-real-eval
        (cdr polynomial) x y z zero one))
    zero))

(defun putnam-1987-a4-complex-add (left right)
  (cons
   (putnam-1987-a4-add
    (car left) (car right))
   (putnam-1987-a4-add
    (cdr left) (cdr right))))

(defun putnam-1987-a4-complex-multiply (left right)
  (cons
   (putnam-1987-a4-subtract
    (putnam-1987-a4-multiply
     (car left) (car right))
    (putnam-1987-a4-multiply
     (cdr left) (cdr right)))
   (putnam-1987-a4-add
    (putnam-1987-a4-multiply
     (car left) (cdr right))
    (putnam-1987-a4-multiply
     (cdr left) (car right)))))

(defun putnam-1987-a4-complex-power
    (value n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons one zero)
    (putnam-1987-a4-complex-multiply
     value
     (putnam-1987-a4-complex-power
      value (- n 1) zero one))))

(defun putnam-1987-a4-monomial-complex-eval
    (monomial x y z zero one)
  (putnam-1987-a4-complex-multiply
   (cons (nth 0 monomial) zero)
   (putnam-1987-a4-complex-multiply
    (putnam-1987-a4-complex-power
     x (nth 1 monomial) zero one)
    (putnam-1987-a4-complex-multiply
     (putnam-1987-a4-complex-power
      y (nth 2 monomial) zero one)
     (putnam-1987-a4-complex-power
      z (nth 3 monomial) zero one)))))

(defun putnam-1987-a4-polynomial-complex-eval
    (polynomial x y z zero one)
  (if (consp polynomial)
      (putnam-1987-a4-complex-add
       (putnam-1987-a4-monomial-complex-eval
        (car polynomial) x y z zero one)
       (putnam-1987-a4-polynomial-complex-eval
        (cdr polynomial) x y z zero one))
    (cons zero zero)))

(defun putnam-1987-a4-complex-zero-p (value zero)
  (and
   (equal (car value) zero)
   (equal (cdr value) zero)))

(defun putnam-1987-a4-distance
    (left-real left-imag right-real right-imag)
  (let ((real-difference
         (putnam-1987-a4-subtract
          left-real right-real))
        (imaginary-difference
         (putnam-1987-a4-subtract
          left-imag right-imag)))
    (putnam-1987-a4-square-root
     (putnam-1987-a4-add
      (putnam-1987-a4-multiply
       real-difference real-difference)
      (putnam-1987-a4-multiply
       imaginary-difference imaginary-difference)))))

(defun-sk putnam-1987-a4-universal-identity-p
    (polynomial zero one)
  (forall (x y z u)
    (implies
     (and
      (putnam-1987-a4-real-p x)
      (putnam-1987-a4-real-p y)
      (putnam-1987-a4-real-p z)
      (putnam-1987-a4-real-p u))
     (equal
      (putnam-1987-a4-polynomial-real-eval
       polynomial
       (putnam-1987-a4-multiply u x)
       (putnam-1987-a4-multiply u y)
       (putnam-1987-a4-multiply u z)
       zero one)
      (putnam-1987-a4-multiply
       (putnam-1987-a4-multiply u u)
       (putnam-1987-a4-f
        (putnam-1987-a4-subtract y x)
        (putnam-1987-a4-subtract z x)))))))

(defun putnam-1987-a4-coordinate-values-p
    (polynomial zero one)
  (and
   (equal
    (putnam-1987-a4-polynomial-real-eval
     polynomial one zero zero zero one)
    (putnam-1987-a4-field-natural
     4 zero one))
   (equal
    (putnam-1987-a4-polynomial-real-eval
     polynomial zero one zero zero one)
    (putnam-1987-a4-field-natural
     5 zero one))
   (equal
    (putnam-1987-a4-polynomial-real-eval
     polynomial zero zero one zero one)
    (putnam-1987-a4-field-natural
     6 zero one))))

(defun putnam-1987-a4-complex-root-p
    (polynomial
     a-real a-imag b-real b-imag c-real c-imag
     zero one)
  (putnam-1987-a4-complex-zero-p
   (putnam-1987-a4-polynomial-complex-eval
    polynomial
    (cons a-real a-imag)
    (cons b-real b-imag)
    (cons c-real c-imag)
    zero one)
   zero))

(defun-sk putnambench-putnam-1987-a4-statement ()
  (forall
   (polynomial zero one
               a-real a-imag
               b-real b-imag
               c-real c-imag)
   (implies
    (and
     (putnam-1987-a4-real-closed-field-p
      zero one)
     (putnam-1987-a4-f-real-valued-p)
     (putnam-1987-a4-polynomial-p
      polynomial)
     (putnam-1987-a4-real-list-p
      (list
       a-real a-imag
       b-real b-imag
       c-real c-imag))
     (putnam-1987-a4-universal-identity-p
      polynomial zero one)
     (putnam-1987-a4-coordinate-values-p
      polynomial zero one)
     (putnam-1987-a4-complex-root-p
      polynomial
      a-real a-imag
      b-real b-imag
      c-real c-imag
      zero one)
     (equal
      (putnam-1987-a4-distance
       b-real b-imag a-real a-imag)
      (putnam-1987-a4-field-natural
       10 zero one)))
    (equal
     (putnam-1987-a4-distance
      c-real c-imag a-real a-imag)
     (putnam-1987-a4-multiply
      (putnam-1987-a4-field-rational
       5 3 zero one)
      (putnam-1987-a4-square-root
       (putnam-1987-a4-field-natural
        30 zero one)))))))

(value-triple :itpeval-statement-checked)
:q
