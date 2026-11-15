;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__041, "Puiseux's Theorem": over an algebraically
;; closed field of characteristic zero, every positive-degree polynomial with
;; coefficients in the full field of lower-bounded, bounded-denominator
;; rational-exponent formal Puiseux series has a Puiseux-series root. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The following conservative interfaces represent an arbitrary coefficient
;; field and rational-indexed series. All typing, field laws, support
;; conditions, extensionality, and coefficient laws are hypotheses of the
;; final statement; the stubs themselves assert no mathematical facts.

(defstub ht041-base-member-p (field value) t)
(defstub ht041-base-zero (field) t)
(defstub ht041-base-one (field) t)
(defstub ht041-base-add (field left right) t)
(defstub ht041-base-mul (field left right) t)
(defstub ht041-base-neg (field value) t)
(defstub ht041-base-inv (field value) t)

(defstub ht041-series-coeff (field series exponent) t)
(defstub ht041-series-zero (field) t)
(defstub ht041-series-one (field) t)
(defstub ht041-series-monomial (field coefficient exponent) t)
(defstub ht041-series-add (field left right) t)
(defstub ht041-series-mul (field left right) t)
(defstub ht041-series-from-coefficients
  (field coefficient-function) t)

;; Coefficient-field structure.

(defun-sk ht041-base-field-laws-p (field)
  (forall (x y z)
    (and
     (implies
      (ht041-base-member-p field x)
      (and
       (ht041-base-member-p field (ht041-base-neg field x))
       (ht041-base-member-p field (ht041-base-inv field x))
       (equal
        (ht041-base-add field x (ht041-base-zero field))
        x)
       (equal
        (ht041-base-add field x (ht041-base-neg field x))
        (ht041-base-zero field))
       (equal
        (ht041-base-mul field x (ht041-base-one field))
        x)
       (implies
        (not (equal x (ht041-base-zero field)))
        (equal
         (ht041-base-mul field x (ht041-base-inv field x))
         (ht041-base-one field)))))
     (implies
      (and
       (ht041-base-member-p field x)
       (ht041-base-member-p field y))
      (and
       (ht041-base-member-p
        field (ht041-base-add field x y))
       (ht041-base-member-p
        field (ht041-base-mul field x y))
       (equal
        (ht041-base-add field x y)
        (ht041-base-add field y x))
       (equal
        (ht041-base-mul field x y)
        (ht041-base-mul field y x))))
     (implies
      (and
       (ht041-base-member-p field x)
       (ht041-base-member-p field y)
       (ht041-base-member-p field z))
      (and
       (equal
        (ht041-base-add
         field (ht041-base-add field x y) z)
        (ht041-base-add
         field x (ht041-base-add field y z)))
       (equal
        (ht041-base-mul
         field (ht041-base-mul field x y) z)
        (ht041-base-mul
         field x (ht041-base-mul field y z)))
       (equal
        (ht041-base-mul
         field x (ht041-base-add field y z))
        (ht041-base-add
         field
         (ht041-base-mul field x y)
         (ht041-base-mul field x z))))))))

(defun ht041-base-field-structure-p (field)
  (and
   (ht041-base-member-p field (ht041-base-zero field))
   (ht041-base-member-p field (ht041-base-one field))
   (not
    (equal
     (ht041-base-zero field)
     (ht041-base-one field)))
   (ht041-base-field-laws-p field)))

(defun ht041-base-nat-scalar (field n)
  (if (zp n)
      (ht041-base-zero field)
    (ht041-base-add
     field
     (ht041-base-one field)
     (ht041-base-nat-scalar field (1- n)))))

(defun-sk ht041-base-characteristic-zero-p (field)
  (forall (n)
    (implies
     (and (natp n)
          (< 0 n))
     (not
      (equal
       (ht041-base-nat-scalar field n)
       (ht041-base-zero field))))))

;; Finite coefficient lists, in ascending degree order, are the canonical
;; representation of ordinary univariate polynomials over the base field.

(defun ht041-base-polynomial-p (field coefficients)
  (if (consp coefficients)
      (and
       (ht041-base-member-p field (car coefficients))
       (ht041-base-polynomial-p field (cdr coefficients)))
    (equal coefficients nil)))

(defun ht041-leading-coefficient (coefficients)
  (if (consp (cdr coefficients))
      (ht041-leading-coefficient (cdr coefficients))
    (car coefficients)))

(defun ht041-base-positive-degree-polynomial-p
    (field coefficients)
  (and
   (ht041-base-polynomial-p field coefficients)
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (ht041-leading-coefficient coefficients)
     (ht041-base-zero field)))))

(defun ht041-base-polynomial-eval
    (field coefficients argument)
  (if (consp coefficients)
      (ht041-base-add
       field
       (car coefficients)
       (ht041-base-mul
        field
        argument
        (ht041-base-polynomial-eval
         field (cdr coefficients) argument)))
    (ht041-base-zero field)))

(defun-sk ht041-base-polynomial-has-root-p
    (field coefficients)
  (exists (root)
    (and
     (ht041-base-member-p field root)
     (equal
      (ht041-base-polynomial-eval
       field coefficients root)
      (ht041-base-zero field)))))

(defun-sk ht041-base-algebraically-closed-p (field)
  (forall (coefficients)
    (implies
     (ht041-base-positive-degree-polynomial-p
      field coefficients)
     (ht041-base-polynomial-has-root-p
      field coefficients))))

(defun ht041-algebraically-closed-char-zero-field-p (field)
  (and
   (ht041-base-field-structure-p field)
   (ht041-base-characteristic-zero-p field)
   (ht041-base-algebraically-closed-p field)))

;; A formal Puiseux series is a genuine coefficient function on all rational
;; exponents. Its support is bounded below and all supported exponents have a
;; common positive denominator. The condition INTEGERP(D*Q) is equivalent to
;; the reduced denominator of rational Q dividing the positive integer D.

(defun-sk ht041-series-coefficients-typed-p (field series)
  (forall (q)
    (implies
     (rationalp q)
     (ht041-base-member-p
      field (ht041-series-coeff field series q)))))

(defun-sk ht041-series-support-above-p
    (field series lower-bound)
  (forall (q)
    (implies
     (and
      (rationalp q)
      (< q lower-bound))
     (equal
      (ht041-series-coeff field series q)
      (ht041-base-zero field)))))

(defun-sk ht041-series-denominator-bounded-p
    (field series common-denominator)
  (forall (q)
    (implies
     (and
      (rationalp q)
      (not
       (equal
        (ht041-series-coeff field series q)
        (ht041-base-zero field))))
     (integerp (* common-denominator q)))))

(defun-sk ht041-series-support-condition-p (field series)
  (exists (lower-bound common-denominator)
    (and
     (rationalp lower-bound)
     (natp common-denominator)
     (< 0 common-denominator)
     (ht041-series-support-above-p
      field series lower-bound)
     (ht041-series-denominator-bounded-p
      field series common-denominator))))

(defun ht041-puiseux-series-p (field series)
  (and
   (ht041-series-coefficients-typed-p field series)
   (ht041-series-support-condition-p field series)))

;; APPLY$ function objects provide ACL2's native representation of function
;; arguments. The realization clauses below ensure that the series carrier
;; contains every tame coefficient function satisfying the Puiseux support
;; conditions, rather than only the finitely supported functions generated by
;; zero, one, monomials, addition, and multiplication.

(defun ht041-coefficient-function-value
    (coefficient-function exponent)
  (apply$ coefficient-function (list exponent)))

(defun-sk ht041-coefficient-function-typed-p
    (field coefficient-function)
  (forall (q)
    (implies
     (rationalp q)
     (ht041-base-member-p
      field
      (ht041-coefficient-function-value
       coefficient-function q)))))

(defun-sk ht041-coefficient-function-support-above-p
    (field coefficient-function lower-bound)
  (forall (q)
    (implies
     (and
      (rationalp q)
      (< q lower-bound))
     (equal
      (ht041-coefficient-function-value
       coefficient-function q)
      (ht041-base-zero field)))))

(defun-sk ht041-coefficient-function-denominator-bounded-p
    (field coefficient-function common-denominator)
  (forall (q)
    (implies
     (and
      (rationalp q)
      (not
       (equal
        (ht041-coefficient-function-value
         coefficient-function q)
        (ht041-base-zero field))))
     (integerp (* common-denominator q)))))

(defun-sk ht041-coefficient-function-support-condition-p
    (field coefficient-function)
  (exists (lower-bound common-denominator)
    (and
     (rationalp lower-bound)
     (natp common-denominator)
     (< 0 common-denominator)
     (ht041-coefficient-function-support-above-p
      field coefficient-function lower-bound)
     (ht041-coefficient-function-denominator-bounded-p
      field coefficient-function common-denominator))))

(defun ht041-admissible-coefficient-function-p
    (field coefficient-function)
  (and
   (tamep-functionp coefficient-function)
   (ht041-coefficient-function-typed-p
    field coefficient-function)
   (ht041-coefficient-function-support-condition-p
    field coefficient-function)))

(defun-sk ht041-series-realizes-coefficient-function-p
    (field coefficient-function series)
  (forall (q)
    (implies
     (rationalp q)
     (equal
      (ht041-series-coeff field series q)
      (ht041-coefficient-function-value
       coefficient-function q)))))

(defun-sk ht041-series-carrier-complete-p (field)
  (forall (coefficient-function)
    (implies
     (ht041-admissible-coefficient-function-p
      field coefficient-function)
     (and
      (ht041-puiseux-series-p
       field
       (ht041-series-from-coefficients
        field coefficient-function))
      (ht041-series-realizes-coefficient-function-p
       field
       coefficient-function
       (ht041-series-from-coefficients
        field coefficient-function))))))

(defun-sk ht041-series-coefficients-equal-p
    (field left right)
  (forall (q)
    (implies
     (rationalp q)
     (equal
      (ht041-series-coeff field left q)
      (ht041-series-coeff field right q)))))

(defun-sk ht041-series-extensionality-p (field)
  (forall (left right)
    (implies
     (and
      (ht041-puiseux-series-p field left)
      (ht041-puiseux-series-p field right)
      (ht041-series-coefficients-equal-p
       field left right))
     (equal left right))))

;; Zero, one, and every rational monomial are represented with their exact
;; coefficient functions. These clauses guarantee a nontrivial, unbounded
;; Puiseux carrier rather than a finite or tag-only surrogate.

(defun-sk ht041-series-zero-coeff-law-p (field)
  (forall (q)
    (implies
     (rationalp q)
     (equal
      (ht041-series-coeff
       field (ht041-series-zero field) q)
      (ht041-base-zero field)))))

(defun-sk ht041-series-one-coeff-law-p (field)
  (forall (q)
    (implies
     (rationalp q)
     (equal
      (ht041-series-coeff
       field (ht041-series-one field) q)
      (if (equal q 0)
          (ht041-base-one field)
        (ht041-base-zero field))))))

(defun-sk ht041-series-monomial-closure-p (field)
  (forall (coefficient exponent)
    (implies
     (and
      (ht041-base-member-p field coefficient)
      (rationalp exponent))
     (ht041-puiseux-series-p
      field
      (ht041-series-monomial
       field coefficient exponent)))))

(defun-sk ht041-series-monomial-coeff-law-p (field)
  (forall (coefficient exponent q)
    (implies
     (and
      (ht041-base-member-p field coefficient)
      (rationalp exponent)
      (rationalp q))
     (equal
      (ht041-series-coeff
       field
       (ht041-series-monomial
        field coefficient exponent)
       q)
      (if (equal q exponent)
          coefficient
        (ht041-base-zero field))))))

;; Addition is pointwise.

(defun-sk ht041-series-add-closure-p (field)
  (forall (left right)
    (implies
     (and
      (ht041-puiseux-series-p field left)
      (ht041-puiseux-series-p field right))
     (ht041-puiseux-series-p
      field (ht041-series-add field left right)))))

(defun-sk ht041-series-add-coeff-law-p (field)
  (forall (left right q)
    (implies
     (and
      (ht041-puiseux-series-p field left)
      (ht041-puiseux-series-p field right)
      (rationalp q))
     (equal
      (ht041-series-coeff
       field (ht041-series-add field left right) q)
      (ht041-base-add
       field
       (ht041-series-coeff field left q)
       (ht041-series-coeff field right q))))))

;; Multiplication is the exact Cauchy product. For fixed Q, bounded support and
;; a common denominator make the set of nonzero contributing exponents finite.
;; INDICES is only a local witness enumerating that mathematically finite set;
;; completeness below quantifies over every rational exponent, so it is not a
;; finite-table replacement for either a series or its multiplication.

(defun ht041-contributing-exponent-p
    (field left right target exponent)
  (and
   (rationalp exponent)
   (not
    (equal
     (ht041-series-coeff field left exponent)
     (ht041-base-zero field)))
   (not
    (equal
     (ht041-series-coeff
      field right (- target exponent))
     (ht041-base-zero field)))))

(defun ht041-convolution-index-list-p
    (field left right target indices)
  (if (consp indices)
      (and
       (ht041-contributing-exponent-p
        field left right target (car indices))
       (not (member-equal (car indices) (cdr indices)))
       (ht041-convolution-index-list-p
        field left right target (cdr indices)))
    (equal indices nil)))

(defun-sk ht041-convolution-index-complete-p
    (field left right target indices)
  (forall (exponent)
    (implies
     (ht041-contributing-exponent-p
      field left right target exponent)
     (member-equal exponent indices))))

(defun ht041-convolution-sum
    (field left right target indices)
  (if (consp indices)
      (ht041-base-add
       field
       (ht041-base-mul
        field
        (ht041-series-coeff
         field left (car indices))
        (ht041-series-coeff
         field right (- target (car indices))))
       (ht041-convolution-sum
        field left right target (cdr indices)))
    (ht041-base-zero field)))

(defun-sk ht041-product-coefficient-correct-p
    (field left right target)
  (exists (indices)
    (and
     (ht041-convolution-index-list-p
      field left right target indices)
     (ht041-convolution-index-complete-p
      field left right target indices)
     (equal
      (ht041-series-coeff
       field (ht041-series-mul field left right) target)
      (ht041-convolution-sum
       field left right target indices)))))

(defun-sk ht041-series-mul-closure-p (field)
  (forall (left right)
    (implies
     (and
      (ht041-puiseux-series-p field left)
      (ht041-puiseux-series-p field right))
     (ht041-puiseux-series-p
      field (ht041-series-mul field left right)))))

(defun-sk ht041-series-mul-coeff-law-p (field)
  (forall (left right q)
    (implies
     (and
      (ht041-puiseux-series-p field left)
      (ht041-puiseux-series-p field right)
      (rationalp q))
     (ht041-product-coefficient-correct-p
      field left right q))))

(defun ht041-puiseux-interface-p (field)
  (and
   (ht041-puiseux-series-p
    field (ht041-series-zero field))
   (ht041-puiseux-series-p
    field (ht041-series-one field))
   (ht041-series-zero-coeff-law-p field)
   (ht041-series-one-coeff-law-p field)
   (ht041-series-monomial-closure-p field)
   (ht041-series-monomial-coeff-law-p field)
   (ht041-series-add-closure-p field)
   (ht041-series-add-coeff-law-p field)
   (ht041-series-mul-closure-p field)
   (ht041-series-mul-coeff-law-p field)
   (ht041-series-carrier-complete-p field)
   (ht041-series-extensionality-p field)))

;; Polynomials over Puiseux series are again canonical finite coefficient
;; lists in ascending degree order. Horner evaluation uses the exact series
;; addition and Cauchy multiplication specified above.

(defun ht041-puiseux-polynomial-p (field coefficients)
  (if (consp coefficients)
      (and
       (ht041-puiseux-series-p field (car coefficients))
       (ht041-puiseux-polynomial-p
        field (cdr coefficients)))
    (equal coefficients nil)))

(defun ht041-positive-degree-puiseux-polynomial-p
    (field coefficients)
  (and
   (ht041-puiseux-polynomial-p field coefficients)
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (ht041-leading-coefficient coefficients)
     (ht041-series-zero field)))))

(defun ht041-puiseux-polynomial-eval
    (field coefficients argument)
  (if (consp coefficients)
      (ht041-series-add
       field
       (car coefficients)
       (ht041-series-mul
        field
        argument
        (ht041-puiseux-polynomial-eval
         field (cdr coefficients) argument)))
    (ht041-series-zero field)))

(defun-sk ht041-puiseux-polynomial-has-root-p
    (field coefficients)
  (exists (root)
    (and
     (ht041-puiseux-series-p field root)
     (equal
      (ht041-puiseux-polynomial-eval
       field coefficients root)
      (ht041-series-zero field)))))

(defun-sk hundred-theorems-041-puiseux-theorem-statement ()
  (forall (field coefficients)
    (implies
     (and
      (ht041-algebraically-closed-char-zero-field-p field)
      (ht041-puiseux-interface-p field)
      (ht041-positive-degree-puiseux-polynomial-p
       field coefficients))
     (ht041-puiseux-polynomial-has-root-p
      field coefficients))))

(value-triple :itpeval-statement-checked)
:q
