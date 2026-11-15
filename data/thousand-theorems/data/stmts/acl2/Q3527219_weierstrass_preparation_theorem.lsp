;; Statement-only formalization of thousand-theorems corpus artifact Q3527219,
;; "Weierstrass preparation theorem": every power series over an arbitrary
;; commutative local ring complete and separated for its maximal-ideal adic
;; filtration, whose residue series is nonzero, factors as a distinguished
;; polynomial times a unit power series. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame ACL2 function objects represent arbitrary carriers, operations,
;; ideals, and coefficient functions.  They are not finite tables.  Every
;; algebraic, local-ring, ideal-power, completeness, and typing condition used
;; by the source theorem is explicit below.

(defun q3527219-member-p (predicate value)
  (if (apply$ predicate (list value)) t nil))

(defun q3527219-unary-value (operation value)
  (apply$ operation (list value)))

(defun q3527219-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun q3527219-negate (negation value)
  (q3527219-unary-value negation value))

(defun q3527219-add (addition left right)
  (q3527219-binary-value addition left right))

(defun q3527219-multiply (multiplication left right)
  (q3527219-binary-value multiplication left right))

(defun q3527219-coeff (series n)
  (q3527219-unary-value series n))

;; Commutative rings.

(defun-sk q3527219-commutative-ring-laws-p
    (carrier zero one addition multiplication negation)
  (forall (x y z)
    (and
     (implies
      (q3527219-member-p carrier x)
      (and
       (q3527219-member-p
        carrier (q3527219-negate negation x))
       (equal (q3527219-add addition x zero) x)
       (equal (q3527219-add addition zero x) x)
       (equal
        (q3527219-add
         addition x (q3527219-negate negation x))
        zero)
       (equal
        (q3527219-add
         addition (q3527219-negate negation x) x)
        zero)
       (equal (q3527219-multiply multiplication x one) x)
       (equal (q3527219-multiply multiplication one x) x)))
     (implies
      (and
       (q3527219-member-p carrier x)
       (q3527219-member-p carrier y))
      (and
       (q3527219-member-p
        carrier (q3527219-add addition x y))
       (q3527219-member-p
        carrier (q3527219-multiply multiplication x y))
       (equal
        (q3527219-add addition x y)
        (q3527219-add addition y x))
       (equal
        (q3527219-multiply multiplication x y)
        (q3527219-multiply multiplication y x))))
     (implies
      (and
       (q3527219-member-p carrier x)
       (q3527219-member-p carrier y)
       (q3527219-member-p carrier z))
      (and
       (equal
        (q3527219-add
         addition (q3527219-add addition x y) z)
        (q3527219-add
         addition x (q3527219-add addition y z)))
       (equal
        (q3527219-multiply
         multiplication
         (q3527219-multiply multiplication x y)
         z)
        (q3527219-multiply
         multiplication
         x
         (q3527219-multiply multiplication y z)))
       (equal
        (q3527219-multiply
         multiplication
         x
         (q3527219-add addition y z))
        (q3527219-add
         addition
         (q3527219-multiply multiplication x y)
         (q3527219-multiply multiplication x z)))
       (equal
        (q3527219-multiply
         multiplication
         (q3527219-add addition x y)
         z)
        (q3527219-add
         addition
         (q3527219-multiply multiplication x z)
         (q3527219-multiply multiplication y z))))))))

(defun q3527219-commutative-ring-p
    (carrier zero one addition multiplication negation)
  (and
   (tamep-functionp carrier)
   (tamep-functionp addition)
   (tamep-functionp multiplication)
   (tamep-functionp negation)
   (q3527219-member-p carrier zero)
   (q3527219-member-p carrier one)
   (not (equal zero one))
   (q3527219-commutative-ring-laws-p
    carrier zero one addition multiplication negation)))

;; The source maximal ideal.  In a commutative local ring it is precisely the
;; set of nonunits; this characterization is bidirectionally equivalent to
;; the usual unique-maximal-ideal definition.

(defun-sk q3527219-ring-unit-p
    (carrier one multiplication value)
  (exists (inverse)
    (and
     (q3527219-member-p carrier inverse)
     (equal
      (q3527219-multiply multiplication value inverse)
      one))))

(defun-sk q3527219-ideal-laws-p
    (carrier zero addition multiplication negation ideal)
  (forall (a x y)
    (and
     (implies
      (q3527219-member-p ideal x)
      (and
       (q3527219-member-p carrier x)
       (q3527219-member-p
        ideal (q3527219-negate negation x))))
     (implies
      (and
       (q3527219-member-p ideal x)
       (q3527219-member-p ideal y))
      (q3527219-member-p
       ideal (q3527219-add addition x y)))
     (implies
      (and
       (q3527219-member-p carrier a)
       (q3527219-member-p ideal x))
      (q3527219-member-p
       ideal (q3527219-multiply multiplication a x))))))

(defun q3527219-ideal-p
    (carrier zero addition multiplication negation ideal)
  (and
   (tamep-functionp ideal)
   (q3527219-member-p ideal zero)
   (q3527219-ideal-laws-p
    carrier zero addition multiplication negation ideal)))

(defun-sk q3527219-nonunits-exactly-ideal-p
    (carrier one multiplication ideal)
  (forall (x)
    (implies
     (q3527219-member-p carrier x)
     (iff
      (q3527219-member-p ideal x)
      (not
       (q3527219-ring-unit-p
        carrier one multiplication x))))))

(defun q3527219-commutative-local-ring-p
    (carrier zero one addition multiplication negation maximal-ideal)
  (and
   (q3527219-commutative-ring-p
    carrier zero one addition multiplication negation)
   (q3527219-ideal-p
    carrier zero addition multiplication negation maximal-ideal)
   (not (q3527219-member-p maximal-ideal one))
   (q3527219-nonunits-exactly-ideal-p
    carrier one multiplication maximal-ideal)))

;; Membership in I^n is represented exactly by an unbounded finite sum of
;; products of n elements of I.  The n = 0 power is the whole ring.

(defun q3527219-ideal-factor-list-p (ideal n factors)
  (and
   (true-listp factors)
   (equal (len factors) (nfix n))
   (if (consp factors)
       (and
        (q3527219-member-p ideal (car factors))
        (q3527219-ideal-factor-list-p
         ideal (- (nfix n) 1) (cdr factors)))
     (zp n))))

(defun q3527219-product-list
    (one multiplication factors)
  (if (consp factors)
      (q3527219-multiply
       multiplication
       (car factors)
       (q3527219-product-list
        one multiplication (cdr factors)))
    one))

(defun q3527219-ideal-product-list-p
    (ideal n products)
  (if (consp products)
      (and
       (q3527219-ideal-factor-list-p
        ideal n (car products))
       (q3527219-ideal-product-list-p
        ideal n (cdr products)))
    (equal products nil)))

(defun q3527219-sum-products
    (zero one addition multiplication products)
  (if (consp products)
      (q3527219-add
       addition
       (q3527219-product-list
        one multiplication (car products))
       (q3527219-sum-products
        zero one addition multiplication (cdr products)))
    zero))

(defun-sk q3527219-positive-ideal-power-member-p
    (zero one addition multiplication ideal n value)
  (exists (products)
    (and
     (true-listp products)
     (q3527219-ideal-product-list-p ideal n products)
     (equal
      value
      (q3527219-sum-products
       zero one addition multiplication products)))))

(defun q3527219-ideal-power-member-p
    (carrier zero one addition multiplication ideal n value)
  (and
   (natp n)
   (q3527219-member-p carrier value)
   (if (zp n)
       t
     (q3527219-positive-ideal-power-member-p
      zero one addition multiplication ideal n value))))

;; Mathlib's IsAdicComplete is exactly separatedness plus convergence of every
;; sequence satisfying f(m) = f(n) modulo I^m whenever m <= n.

(defun-sk q3527219-in-every-ideal-power-p
    (carrier zero one addition multiplication ideal value)
  (forall (n)
    (implies
     (natp n)
     (q3527219-ideal-power-member-p
      carrier zero one addition multiplication ideal n value))))

(defun-sk q3527219-adic-hausdorff-p
    (carrier zero one addition multiplication ideal)
  (forall (value)
    (implies
     (and
      (q3527219-member-p carrier value)
      (q3527219-in-every-ideal-power-p
       carrier zero one addition multiplication ideal value))
     (equal value zero))))

(defun-sk q3527219-sequence-typed-p (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (q3527219-member-p
      carrier (q3527219-coeff sequence n)))))

(defun-sk q3527219-adic-cauchy-p
    (carrier zero one addition multiplication negation ideal sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (<= m n))
     (q3527219-ideal-power-member-p
      carrier zero one addition multiplication ideal m
      (q3527219-add
       addition
       (q3527219-coeff sequence m)
       (q3527219-negate
        negation (q3527219-coeff sequence n)))))))

(defun-sk q3527219-adic-limit-p
    (carrier zero one addition multiplication negation ideal sequence limit)
  (forall (n)
    (implies
     (natp n)
     (q3527219-ideal-power-member-p
      carrier zero one addition multiplication ideal n
      (q3527219-add
       addition
       (q3527219-coeff sequence n)
       (q3527219-negate negation limit))))))

(defun-sk q3527219-adic-converges-p
    (carrier zero one addition multiplication negation ideal sequence)
  (exists (limit)
    (and
     (q3527219-member-p carrier limit)
     (q3527219-adic-limit-p
      carrier zero one addition multiplication negation
      ideal sequence limit))))

(defun-sk q3527219-adic-precomplete-p
    (carrier zero one addition multiplication negation ideal)
  (forall (sequence)
    (implies
     (and
      (tamep-functionp sequence)
      (q3527219-sequence-typed-p carrier sequence)
      (q3527219-adic-cauchy-p
       carrier zero one addition multiplication negation
       ideal sequence))
     (q3527219-adic-converges-p
      carrier zero one addition multiplication negation
      ideal sequence))))

(defun q3527219-adic-complete-p
    (carrier zero one addition multiplication negation ideal)
  (and
   (q3527219-adic-hausdorff-p
    carrier zero one addition multiplication ideal)
   (q3527219-adic-precomplete-p
    carrier zero one addition multiplication negation ideal)))

;; Formal power series are arbitrary tame coefficient functions N -> A.

(defun q3527219-power-series-p (carrier series)
  (and
   (tamep-functionp series)
   (q3527219-sequence-typed-p carrier series)))

(defun-sk q3527219-residue-series-nonzero-p
    (maximal-ideal series)
  (exists (n)
    (and
     (natp n)
     (not
      (q3527219-member-p
       maximal-ideal (q3527219-coeff series n))))))

;; Finite coefficient lists in ascending degree order represent polynomials.

(defun q3527219-ring-list-p (carrier values)
  (if (consp values)
      (and
       (q3527219-member-p carrier (car values))
       (q3527219-ring-list-p carrier (cdr values)))
    (equal values nil)))

(defun q3527219-polynomial-coeff (zero polynomial n)
  (if (< (nfix n) (len polynomial))
      (nth (nfix n) polynomial)
    zero))

(defun-sk q3527219-lower-coefficients-in-ideal-p
    (zero maximal-ideal polynomial)
  (forall (n)
    (implies
     (and
      (natp n)
      (< n (- (len polynomial) 1)))
     (q3527219-member-p
      maximal-ideal
      (q3527219-polynomial-coeff zero polynomial n)))))

(defun q3527219-distinguished-polynomial-p
    (carrier zero one maximal-ideal polynomial)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (q3527219-ring-list-p carrier polynomial)
   (equal (car (last polynomial)) one)
   (q3527219-lower-coefficients-in-ideal-p
    zero maximal-ideal polynomial)))

;; Coefficients of products are the exact finite Cauchy convolution.

(defun q3527219-series-product-prefix
    (zero addition multiplication left right n count)
  (if (zp count)
      zero
    (let ((i (- (nfix count) 1)))
      (q3527219-add
       addition
       (q3527219-multiply
        multiplication
        (q3527219-coeff left i)
        (q3527219-coeff right (- (nfix n) i)))
       (q3527219-series-product-prefix
        zero addition multiplication left right
        n (- (nfix count) 1))))))

(defun q3527219-series-product-coeff
    (zero addition multiplication left right n)
  (q3527219-series-product-prefix
   zero addition multiplication left right
   (nfix n) (+ 1 (nfix n))))

(defun-sk q3527219-series-product-is-one-p
    (zero one addition multiplication left right)
  (forall (n)
    (implies
     (natp n)
     (equal
      (q3527219-series-product-coeff
       zero addition multiplication left right n)
      (if (zp n) one zero)))))

(defun-sk q3527219-power-series-unit-p
    (carrier zero one addition multiplication series)
  (exists (inverse)
    (and
     (q3527219-power-series-p carrier inverse)
     (q3527219-series-product-is-one-p
      zero one addition multiplication series inverse))))

;; A polynomial is coerced to a power series by zero extension before taking
;; the same Cauchy product.

(defun q3527219-polynomial-series-product-prefix
    (zero addition multiplication polynomial series n count)
  (if (zp count)
      zero
    (let ((i (- (nfix count) 1)))
      (q3527219-add
       addition
       (q3527219-multiply
        multiplication
        (q3527219-polynomial-coeff zero polynomial i)
        (q3527219-coeff series (- (nfix n) i)))
       (q3527219-polynomial-series-product-prefix
        zero addition multiplication polynomial series
        n (- (nfix count) 1))))))

(defun q3527219-polynomial-series-product-coeff
    (zero addition multiplication polynomial series n)
  (q3527219-polynomial-series-product-prefix
   zero addition multiplication polynomial series
   (nfix n) (+ 1 (nfix n))))

(defun-sk q3527219-factorization-equality-p
    (zero addition multiplication series polynomial unit-series)
  (forall (n)
    (implies
     (natp n)
     (equal
      (q3527219-coeff series n)
      (q3527219-polynomial-series-product-coeff
       zero addition multiplication polynomial unit-series n)))))

(defun-sk q3527219-weierstrass-factorization-exists-p
    (carrier zero one addition multiplication
             maximal-ideal series)
  (exists (polynomial unit-series)
    (and
     (q3527219-distinguished-polynomial-p
      carrier zero one maximal-ideal polynomial)
     (q3527219-power-series-p carrier unit-series)
     (q3527219-power-series-unit-p
      carrier zero one addition multiplication unit-series)
     (q3527219-factorization-equality-p
      zero addition multiplication
      series polynomial unit-series))))

(defun-sk
    thousand-theorems-q3527219-weierstrass-preparation-theorem-statement
    ()
  (forall
    (carrier zero one addition multiplication negation
             maximal-ideal series)
    (implies
     (and
      (q3527219-commutative-local-ring-p
       carrier zero one addition multiplication negation
       maximal-ideal)
      (q3527219-adic-complete-p
       carrier zero one addition multiplication negation
       maximal-ideal)
      (q3527219-power-series-p carrier series)
      (q3527219-residue-series-nonzero-p
       maximal-ideal series))
     (q3527219-weierstrass-factorization-exists-p
      carrier zero one addition multiplication
      maximal-ideal series))))

(value-triple :itpeval-statement-checked)
:q
