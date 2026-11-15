;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__018, "Liouville's Theorem and the Construction of
;; Transcendental Numbers": every Liouville real is transcendental, and the
;; real Liouville constant sum_{k>=1} 10^(-k!) is a concrete example. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The general theorem is stated over a real-closed ordered field. This is an
;; algebraic presentation of the real-number operations used by the source and
;; avoids silently restricting the theorem to ACL2's built-in rationals.

(defstub ht018-carrier (x) t)
(defstub ht018-add-op (x y) t)
(defstub ht018-multiply-op (x y) t)
(defstub ht018-negate-op (x) t)
(defstub ht018-inverse-op (x) t)
(defstub ht018-less-op (x y) t)

(defun ht018-member-p (x)
  (if (ht018-carrier x) t nil))

(defun ht018-add (x y)
  (ht018-add-op x y))

(defun ht018-multiply (x y)
  (ht018-multiply-op x y))

(defun ht018-negate (x)
  (ht018-negate-op x))

(defun ht018-inverse (x)
  (ht018-inverse-op x))

(defun ht018-subtract (x y)
  (ht018-add x (ht018-negate y)))

(defun ht018-less (x y)
  (if (ht018-less-op x y) t nil))

(defun-sk ht018-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht018-member-p x)
      (ht018-member-p y)
      (ht018-member-p z))
     (and
      (ht018-member-p (ht018-add x y))
      (ht018-member-p (ht018-multiply x y))
      (ht018-member-p (ht018-negate x))
      (ht018-member-p (ht018-inverse x))
      (equal (ht018-add (ht018-add x y) z)
             (ht018-add x (ht018-add y z)))
      (equal (ht018-add x y)
             (ht018-add y x))
      (equal (ht018-add x zero) x)
      (equal (ht018-add x (ht018-negate x)) zero)
      (equal (ht018-multiply (ht018-multiply x y) z)
             (ht018-multiply x (ht018-multiply y z)))
      (equal (ht018-multiply x y)
             (ht018-multiply y x))
      (equal (ht018-multiply x one) x)
      (equal
       (ht018-multiply x (ht018-add y z))
       (ht018-add
        (ht018-multiply x y)
        (ht018-multiply x z)))
      (implies
       (not (equal x zero))
       (equal
        (ht018-multiply x (ht018-inverse x))
        one))))))

(defun-sk ht018-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht018-member-p x)
      (ht018-member-p y)
      (ht018-member-p z))
     (and
      (not (ht018-less x x))
      (or
       (equal x y)
       (ht018-less x y)
       (ht018-less y x))
      (implies
       (and
        (ht018-less x y)
        (ht018-less y z))
       (ht018-less x z))
      (implies
       (ht018-less x y)
       (ht018-less
        (ht018-add x z)
        (ht018-add y z)))
      (implies
       (and
        (ht018-less zero x)
        (ht018-less zero y))
       (ht018-less zero (ht018-multiply x y)))))))

(defun ht018-carrier-list-p (values)
  (if (consp values)
      (and
       (ht018-member-p (car values))
       (ht018-carrier-list-p (cdr values)))
    (equal values nil)))

(defun ht018-carrier-polynomial-value
    (coefficients x zero)
  (if (consp coefficients)
      (ht018-add
       (car coefficients)
       (ht018-multiply
        x
        (ht018-carrier-polynomial-value
         (cdr coefficients) x zero)))
    zero))

(defun ht018-odd-degree-carrier-polynomial-p
    (coefficients zero)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (ht018-carrier-list-p coefficients)
   (evenp (len coefficients))
   (not (equal (car (last coefficients)) zero))))

(defun-sk ht018-has-square-root-p (x)
  (exists (root)
    (and
     (ht018-member-p root)
     (equal (ht018-multiply root root) x))))

(defun-sk ht018-carrier-polynomial-has-root-p
    (coefficients zero)
  (exists (root)
    (and
     (ht018-member-p root)
     (equal
      (ht018-carrier-polynomial-value
       coefficients root zero)
      zero))))

;; These are the standard first-order real-closedness conditions.
(defun-sk ht018-real-closure-laws-p (zero)
  (forall (x coefficients)
    (and
     (implies
      (and
       (ht018-member-p x)
       (not (ht018-less x zero)))
      (ht018-has-square-root-p x))
     (implies
      (ht018-odd-degree-carrier-polynomial-p
       coefficients zero)
      (ht018-carrier-polynomial-has-root-p
       coefficients zero)))))

(defun ht018-natural-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (ht018-add
     one
     (ht018-natural-value (- n 1) zero one))))

(defun-sk ht018-natural-bound-exists-p (x zero one)
  (exists (n)
    (and
     (natp n)
     (ht018-less
      x
      (ht018-natural-value n zero one)))))

(defun-sk ht018-archimedean-law-p (zero one)
  (forall (x)
    (implies
     (ht018-member-p x)
     (ht018-natural-bound-exists-p x zero one))))

(defun ht018-real-scalar-context-p (zero one)
  (and
   (ht018-member-p zero)
   (ht018-member-p one)
   (not (equal zero one))
   (ht018-less zero one)
   (ht018-field-laws-p zero one)
   (ht018-order-laws-p zero)
   (ht018-real-closure-laws-p zero)
   (ht018-archimedean-law-p zero one)))

(defun ht018-integer-value (integer zero one)
  (if (< integer 0)
      (ht018-negate
       (ht018-natural-value (- integer) zero one))
    (ht018-natural-value integer zero one)))

(defun ht018-power (value exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (ht018-multiply
     value
     (ht018-power value (- exponent 1) one))))

(defun ht018-absolute-value (value zero)
  (if (ht018-less value zero)
      (ht018-negate value)
    value))

(defun ht018-rational-value
    (numerator denominator zero one)
  (ht018-multiply
   (ht018-integer-value numerator zero one)
   (ht018-inverse
    (ht018-integer-value denominator zero one))))

(defun-sk ht018-liouville-approximation-exists-p
    (x exponent zero one)
  (exists (numerator denominator)
    (let* ((approximation
            (ht018-rational-value
             numerator denominator zero one))
           (denominator-value
            (ht018-integer-value denominator zero one))
           (distance
            (ht018-absolute-value
             (ht018-subtract x approximation)
             zero))
           (bound
            (ht018-inverse
             (ht018-power
              denominator-value exponent one))))
      (and
       (integerp numerator)
       (integerp denominator)
       (< 1 denominator)
       (not (equal x approximation))
       (ht018-less distance bound)))))

(defun-sk ht018-liouville-number-p (x zero one)
  (forall (exponent)
    (implies
     (natp exponent)
     (ht018-liouville-approximation-exists-p
      x exponent zero one))))

(defun ht018-field-integer-polynomial-value
    (coefficients x zero one)
  (if (consp coefficients)
      (ht018-add
       (ht018-integer-value (car coefficients) zero one)
       (ht018-multiply
        x
        (ht018-field-integer-polynomial-value
         (cdr coefficients) x zero one)))
    zero))

(defun ht018-integer-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and (integerp (car coefficients))
           (ht018-integer-coefficient-list-p
            (cdr coefficients)))
    (equal coefficients nil)))

(defun ht018-nonzero-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (or (not (equal (car coefficients) 0))
          (ht018-nonzero-coefficient-list-p
           (cdr coefficients)))
    nil))

(defun-sk ht018-algebraic-over-integers-p
    (x zero one)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (ht018-integer-coefficient-list-p coefficients)
     (ht018-nonzero-coefficient-list-p coefficients)
     (equal
      (ht018-field-integer-polynomial-value
       coefficients x zero one)
      zero))))

(defun-sk ht018-general-liouville-theorem-p ()
  (forall (zero one x)
    (implies
     (and
      (ht018-real-scalar-context-p zero one)
      (ht018-member-p x)
      (ht018-liouville-number-p x zero one))
     (not
      (ht018-algebraic-over-integers-p
       x zero one)))))

(defun ht018-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (ht018-factorial (- n 1)))))

;; For natural terms, this is sum_{k=1}^terms 10^(-k!).
(defun ht018-liouville-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (ht018-liouville-prefix (- terms 1))
       (/ 1 (expt 10 (ht018-factorial terms))))))

;; Coefficients are listed in ascending order of exponent.
(defun ht018-polynomial-value (coefficients x)
  (if (consp coefficients)
      (+ (car coefficients)
         (* x
            (ht018-polynomial-value
             (cdr coefficients) x)))
    0))

;; A polynomial vanishes at the real limit represented by the Liouville
;; prefixes exactly when its values on those prefixes converge to zero.
(defun-sk ht018-polynomial-zero-tail-p
  (coefficients epsilon cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (abs
       (ht018-polynomial-value
        coefficients
        (ht018-liouville-prefix index)))
      epsilon))))

(defun-sk ht018-polynomial-zero-cutoff-exists-p
  (coefficients epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht018-polynomial-zero-tail-p
      coefficients epsilon cutoff))))

(defun-sk ht018-polynomial-tends-to-zero-p (coefficients)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (ht018-polynomial-zero-cutoff-exists-p
      coefficients epsilon))))

(defun-sk ht018-liouville-is-algebraic-p ()
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (ht018-integer-coefficient-list-p coefficients)
     (ht018-nonzero-coefficient-list-p coefficients)
     (ht018-polynomial-tends-to-zero-p coefficients))))

(defun hundred-theorems-018-transcendental-liouville-statement ()
  (and
   (ht018-general-liouville-theorem-p)
   (not (ht018-liouville-is-algebraic-p))))

(value-triple :itpeval-statement-checked)
:q
