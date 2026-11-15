;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_a1:
;; existence of three real polynomials whose signed absolute values equal the
;; specified continuous three-piece linear function. This file contains no
;; proof and does not prescribe a particular polynomial witness.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar symbols present an arbitrary real-closed ordered field. Real
;; closedness is stated by the standard two conditions: every positive scalar
;; has a square root, and every odd-degree polynomial has a root. This is
;; first-order equivalent to the real field for the polynomial formula below.

(defstub p1999a1-scalar-p (x) t)
(defstub p1999a1-add-op (x y) t)
(defstub p1999a1-multiply-op (x y) t)
(defstub p1999a1-negate-op (x) t)
(defstub p1999a1-inverse-op (x) t)
(defstub p1999a1-less-op (x y) t)
(defstub p1999a1-zero () t)
(defstub p1999a1-one () t)

(defun p1999a1-add (x y)
  (p1999a1-add-op x y))

(defun p1999a1-multiply (x y)
  (p1999a1-multiply-op x y))

(defun p1999a1-negate (x)
  (p1999a1-negate-op x))

(defun p1999a1-inverse (x)
  (p1999a1-inverse-op x))

(defun p1999a1-subtract (x y)
  (p1999a1-add x (p1999a1-negate y)))

(defun p1999a1-less (x y)
  (if (p1999a1-less-op x y) t nil))

(defun p1999a1-positive-p (x)
  (and
   (p1999a1-scalar-p x)
   (p1999a1-less (p1999a1-zero) x)))

(defun-sk p1999a1-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p1999a1-scalar-p x)
      (p1999a1-scalar-p y)
      (p1999a1-scalar-p z))
     (and
      (p1999a1-scalar-p (p1999a1-add x y))
      (p1999a1-scalar-p (p1999a1-multiply x y))
      (p1999a1-scalar-p (p1999a1-negate x))
      (implies
       (not (equal x (p1999a1-zero)))
       (p1999a1-scalar-p (p1999a1-inverse x)))
      (equal
       (p1999a1-add (p1999a1-add x y) z)
       (p1999a1-add x (p1999a1-add y z)))
      (equal
       (p1999a1-add x y)
       (p1999a1-add y x))
      (equal
       (p1999a1-add x (p1999a1-zero))
       x)
      (equal
       (p1999a1-add x (p1999a1-negate x))
       (p1999a1-zero))
      (equal
       (p1999a1-multiply
        (p1999a1-multiply x y) z)
       (p1999a1-multiply
        x (p1999a1-multiply y z)))
      (equal
       (p1999a1-multiply x y)
       (p1999a1-multiply y x))
      (equal
       (p1999a1-multiply x (p1999a1-one))
       x)
      (implies
       (not (equal x (p1999a1-zero)))
       (equal
        (p1999a1-multiply x (p1999a1-inverse x))
        (p1999a1-one)))
      (equal
       (p1999a1-multiply x (p1999a1-add y z))
       (p1999a1-add
        (p1999a1-multiply x y)
        (p1999a1-multiply x z)))))))

(defun-sk p1999a1-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p1999a1-scalar-p x)
      (p1999a1-scalar-p y)
      (p1999a1-scalar-p z))
     (and
      (not (p1999a1-less x x))
      (or
       (equal x y)
       (p1999a1-less x y)
       (p1999a1-less y x))
      (implies
       (and
        (p1999a1-less x y)
        (p1999a1-less y z))
       (p1999a1-less x z))
      (implies
       (p1999a1-less x y)
       (p1999a1-less
        (p1999a1-add x z)
        (p1999a1-add y z)))
      (implies
       (and
        (p1999a1-less (p1999a1-zero) x)
        (p1999a1-less (p1999a1-zero) y))
       (p1999a1-less
        (p1999a1-zero)
        (p1999a1-multiply x y)))))))

(defun p1999a1-carrier-list-p (coefficients)
  (if (consp coefficients)
      (and
       (p1999a1-scalar-p (car coefficients))
       (p1999a1-carrier-list-p (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients are stored in increasing degree order.
(defun p1999a1-polynomial-value (coefficients x)
  (if (consp coefficients)
      (p1999a1-add
       (car coefficients)
       (p1999a1-multiply
        x
        (p1999a1-polynomial-value
         (cdr coefficients) x)))
    (p1999a1-zero)))

(defun p1999a1-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (p1999a1-carrier-list-p coefficients)))

(defun p1999a1-odd-degree-polynomial-p (coefficients)
  (and
   (p1999a1-polynomial-p coefficients)
   (consp coefficients)
   ;; Degree LEN-1 is odd exactly when LEN is even.
   (evenp (len coefficients))
   (not
    (equal
     (car (last coefficients))
     (p1999a1-zero)))))

(defun-sk p1999a1-square-root-exists-p (x)
  (exists (root)
    (and
     (p1999a1-scalar-p root)
     (equal
      (p1999a1-multiply root root)
      x))))

(defun-sk p1999a1-positive-square-roots-p ()
  (forall (x)
    (implies
     (p1999a1-positive-p x)
     (p1999a1-square-root-exists-p x))))

(defun-sk p1999a1-polynomial-root-exists-p
    (coefficients)
  (exists (root)
    (and
     (p1999a1-scalar-p root)
     (equal
      (p1999a1-polynomial-value
       coefficients root)
      (p1999a1-zero)))))

(defun-sk p1999a1-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (p1999a1-odd-degree-polynomial-p coefficients)
     (p1999a1-polynomial-root-exists-p
      coefficients))))

(defun p1999a1-real-closed-field-p ()
  (and
   (p1999a1-scalar-p (p1999a1-zero))
   (p1999a1-scalar-p (p1999a1-one))
   (not
    (equal (p1999a1-zero) (p1999a1-one)))
   (p1999a1-less (p1999a1-zero) (p1999a1-one))
   (p1999a1-field-laws-p)
   (p1999a1-order-laws-p)
   (p1999a1-positive-square-roots-p)
   (p1999a1-odd-polynomial-roots-p)))

(defun p1999a1-two ()
  (p1999a1-add
   (p1999a1-one)
   (p1999a1-one)))

(defun p1999a1-three ()
  (p1999a1-add
   (p1999a1-two)
   (p1999a1-one)))

(defun p1999a1-minus-one ()
  (p1999a1-negate (p1999a1-one)))

(defun p1999a1-absolute-value (x)
  (if (p1999a1-less x (p1999a1-zero))
      (p1999a1-negate x)
    x))

(defun p1999a1-source-value (x)
  (if (p1999a1-less x (p1999a1-minus-one))
      (p1999a1-minus-one)
    (if (not (p1999a1-less (p1999a1-zero) x))
        (p1999a1-add
         (p1999a1-multiply (p1999a1-three) x)
         (p1999a1-two))
      (p1999a1-add
       (p1999a1-negate
        (p1999a1-multiply (p1999a1-two) x))
       (p1999a1-two)))))

(defun p1999a1-candidate-value (f g h x)
  (p1999a1-add
   (p1999a1-subtract
    (p1999a1-absolute-value
     (p1999a1-polynomial-value f x))
    (p1999a1-absolute-value
     (p1999a1-polynomial-value g x)))
   (p1999a1-polynomial-value h x)))

(defun-sk p1999a1-polynomial-identity-p (f g h)
  (forall (x)
    (implies
     (p1999a1-scalar-p x)
     (equal
      (p1999a1-candidate-value f g h x)
      (p1999a1-source-value x)))))

(defun p1999a1-polynomial-witness-p (f g h)
  (and
   (p1999a1-polynomial-p f)
   (p1999a1-polynomial-p g)
   (p1999a1-polynomial-p h)
   (p1999a1-polynomial-identity-p f g h)))

(defun-sk p1999a1-polynomials-exist-p ()
  (exists (f g h)
    (p1999a1-polynomial-witness-p f g h)))

(defun putnambench-putnam-1999-a1-statement ()
  (implies
   (p1999a1-real-closed-field-p)
   (p1999a1-polynomials-exist-p)))

(value-triple :itpeval-statement-checked)
:q
