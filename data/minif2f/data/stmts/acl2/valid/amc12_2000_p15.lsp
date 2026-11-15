;; Statement-only formalization of miniF2F artifact amc12_2000_p15:
        ;; an exact duplicate-free enumeration of the complex fiber forced by the source function equation has transformed sum -1/9.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amc00p15-real-p (value) t)
(defstub amc00p15-zero () t)
(defstub amc00p15-one () t)
(defstub amc00p15-add (left right) t)
(defstub amc00p15-mul (left right) t)
(defstub amc00p15-neg (value) t)
(defstub amc00p15-inv (value) t)
(defstub amc00p15-lt (left right) t)
(defstub amc00p15-of-rational (value) t)

(defun amc00p15-sub (left right)
  (amc00p15-add left (amc00p15-neg right)))

(defun amc00p15-div (left right)
  (amc00p15-mul left (amc00p15-inv right)))

(defun amc00p15-le (left right)
  (or (equal left right) (amc00p15-lt left right)))

(defun amc00p15-nonnegative-p (value)
  (and (amc00p15-real-p value)
       (amc00p15-le (amc00p15-zero) value)))

(defun amc00p15-positive-p (value)
  (and (amc00p15-real-p value)
       (amc00p15-lt (amc00p15-zero) value)))

(defun amc00p15-abs (value)
  (if (amc00p15-lt value (amc00p15-zero))
      (amc00p15-neg value)
    value))

(defun amc00p15-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amc00p15-one)
    (amc00p15-mul
     value
     (amc00p15-pow value (1- exponent)))))

(defun-sk amc00p15-field-laws-p ()
  (forall (x y z)
    (and
     (amc00p15-real-p (amc00p15-zero))
     (amc00p15-real-p (amc00p15-one))
     (not (equal (amc00p15-zero) (amc00p15-one)))
     (implies
      (amc00p15-real-p x)
      (and
       (amc00p15-real-p (amc00p15-neg x))
       (amc00p15-real-p (amc00p15-inv x))
       (equal (amc00p15-add x (amc00p15-zero)) x)
       (equal (amc00p15-add x (amc00p15-neg x))
              (amc00p15-zero))
       (equal (amc00p15-mul x (amc00p15-one)) x)
       (implies
        (not (equal x (amc00p15-zero)))
        (equal (amc00p15-mul x (amc00p15-inv x))
               (amc00p15-one)))))
     (equal (amc00p15-inv (amc00p15-zero))
            (amc00p15-zero))
     (implies
      (and (amc00p15-real-p x)
           (amc00p15-real-p y))
      (and
       (amc00p15-real-p (amc00p15-add x y))
       (amc00p15-real-p (amc00p15-mul x y))
       (equal (amc00p15-add x y)
              (amc00p15-add y x))
       (equal (amc00p15-mul x y)
              (amc00p15-mul y x))))
     (implies
      (and (amc00p15-real-p x)
           (amc00p15-real-p y)
           (amc00p15-real-p z))
      (and
       (equal (amc00p15-add (amc00p15-add x y) z)
              (amc00p15-add x (amc00p15-add y z)))
       (equal (amc00p15-mul (amc00p15-mul x y) z)
              (amc00p15-mul x (amc00p15-mul y z)))
       (equal (amc00p15-mul x (amc00p15-add y z))
              (amc00p15-add
               (amc00p15-mul x y)
               (amc00p15-mul x z))))))))

(defun-sk amc00p15-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amc00p15-real-p x)
          (amc00p15-real-p y)
          (amc00p15-real-p z))
     (and
      (not (amc00p15-lt x x))
      (or (equal x y)
          (amc00p15-lt x y)
          (amc00p15-lt y x))
      (implies
       (and (amc00p15-lt x y)
            (amc00p15-lt y z))
       (amc00p15-lt x z))
      (implies
       (amc00p15-lt x y)
       (amc00p15-lt
        (amc00p15-add x z)
        (amc00p15-add y z)))
      (implies
       (and (amc00p15-lt (amc00p15-zero) x)
            (amc00p15-lt (amc00p15-zero) y))
       (amc00p15-lt
        (amc00p15-zero)
        (amc00p15-mul x y)))))))

(defun-sk amc00p15-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amc00p15-real-p (amc00p15-of-rational a))
      (equal (amc00p15-of-rational 0) (amc00p15-zero))
      (equal (amc00p15-of-rational 1) (amc00p15-one))
      (equal
       (amc00p15-of-rational (+ a b))
       (amc00p15-add
        (amc00p15-of-rational a)
        (amc00p15-of-rational b)))
      (equal
       (amc00p15-of-rational (* a b))
       (amc00p15-mul
        (amc00p15-of-rational a)
        (amc00p15-of-rational b)))
      (equal
       (amc00p15-of-rational (- a))
       (amc00p15-neg (amc00p15-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amc00p15-of-rational a)
        (amc00p15-of-rational b)))
      (iff
       (< a b)
       (amc00p15-lt
        (amc00p15-of-rational a)
        (amc00p15-of-rational b)))))))

(defun amc00p15-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc00p15-real-p (car coefficients))
     (amc00p15-polynomial-p (cdr coefficients)))))

(defun amc00p15-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amc00p15-zero)
    (amc00p15-add
     (car coefficients)
     (amc00p15-mul
      x
      (amc00p15-polynomial-value
       (cdr coefficients) x)))))

(defun amc00p15-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc00p15-leading-coefficient (cdr coefficients))))

(defun amc00p15-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc00p15-leading-coefficient coefficients)
     (amc00p15-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc00p15-square-root-exists-p (x)
  (exists (root)
    (and
     (amc00p15-nonnegative-p root)
     (equal (amc00p15-mul root root) x))))

(defun-sk amc00p15-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amc00p15-nonnegative-p x)
     (amc00p15-square-root-exists-p x))))

(defun-sk amc00p15-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amc00p15-real-p root)
     (equal
      (amc00p15-polynomial-value coefficients root)
      (amc00p15-zero)))))

(defun-sk amc00p15-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc00p15-polynomial-p coefficients)
      (amc00p15-odd-degree-p coefficients))
     (amc00p15-polynomial-root-exists-p coefficients))))

(defun amc00p15-real-closed-field-p ()
  (and
   (amc00p15-field-laws-p)
   (amc00p15-order-laws-p)
   (amc00p15-rational-laws-p)
   (amc00p15-lt (amc00p15-zero) (amc00p15-one))
   (amc00p15-nonnegative-square-roots-p)
   (amc00p15-odd-polynomial-roots-p)))

(defun amc00p15-principal-square-root-p (root value)
  (and
   (amc00p15-nonnegative-p root)
   (equal (amc00p15-mul root root) value)))

(defchoose amc00p15-sqrt (root) (value)
  (amc00p15-principal-square-root-p root value))

(defun amc00p15-complex-p (value)
  (and (consp value)
       (amc00p15-real-p (car value))
       (amc00p15-real-p (cdr value))))

(defun amc00p15-complex (real imaginary)
  (cons real imaginary))

(defun amc00p15-complex-zero ()
  (amc00p15-complex (amc00p15-zero) (amc00p15-zero)))

(defun amc00p15-complex-of-rational (value)
  (amc00p15-complex
   (amc00p15-of-rational value)
   (amc00p15-zero)))

(defun amc00p15-complex-add (left right)
  (amc00p15-complex
   (amc00p15-add (car left) (car right))
   (amc00p15-add (cdr left) (cdr right))))

(defun amc00p15-complex-neg (value)
  (amc00p15-complex
   (amc00p15-neg (car value))
   (amc00p15-neg (cdr value))))

(defun amc00p15-complex-sub (left right)
  (amc00p15-complex-add left (amc00p15-complex-neg right)))

(defun amc00p15-complex-mul (left right)
  (amc00p15-complex
   (amc00p15-sub
    (amc00p15-mul (car left) (car right))
    (amc00p15-mul (cdr left) (cdr right)))
   (amc00p15-add
    (amc00p15-mul (car left) (cdr right))
    (amc00p15-mul (cdr left) (car right)))))

(defun amc00p15-complex-norm-square (value)
  (amc00p15-add
   (amc00p15-mul (car value) (car value))
   (amc00p15-mul (cdr value) (cdr value))))

(defun amc00p15-complex-inv (value)
  (let ((denominator
         (amc00p15-complex-norm-square value)))
    (amc00p15-complex
     (amc00p15-div (car value) denominator)
     (amc00p15-neg
      (amc00p15-div (cdr value) denominator)))))

(defun amc00p15-complex-div (left right)
  (amc00p15-complex-mul left (amc00p15-complex-inv right)))

(defun amc00p15-complex-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amc00p15-complex-of-rational 1)
    (amc00p15-complex-mul
     value
     (amc00p15-complex-pow value (1- exponent)))))

(defun amc00p15-complex-norm (value)
  (amc00p15-sqrt (amc00p15-complex-norm-square value)))

        (defun amc00p15-complex-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (amc00p15-complex-p (car values))
     (amc00p15-complex-list-p (cdr values)))))

(defun amc00p15-no-duplicates-p (values)
  (if (endp values)
      t
    (and
     (not (member-equal (car values) (cdr values)))
     (amc00p15-no-duplicates-p (cdr values)))))

(defun amc00p15-source-function (y)
  (amc00p15-complex-add
   (amc00p15-complex-add
    (amc00p15-complex-mul
     (amc00p15-complex-of-rational 9)
     (amc00p15-complex-pow y 2))
    (amc00p15-complex-mul
     (amc00p15-complex-of-rational 3) y))
   (amc00p15-complex-of-rational 1)))

(defun-sk amc00p15-exact-fiber-p (solutions)
  (forall (y)
    (implies
     (amc00p15-complex-p y)
     (iff
      (member-equal y solutions)
      (equal
       (amc00p15-source-function y)
       (amc00p15-complex-of-rational 7))))))

(defun amc00p15-transformed-sum (solutions)
  (if (endp solutions)
      (amc00p15-complex-zero)
    (amc00p15-complex-add
     (amc00p15-complex-div
      (car solutions)
      (amc00p15-complex-of-rational 3))
     (amc00p15-transformed-sum (cdr solutions)))))

(defun-sk amc00p15-result-p ()
  (exists (solutions)
    (and
     (true-listp solutions)
     (amc00p15-complex-list-p solutions)
     (amc00p15-no-duplicates-p solutions)
     (amc00p15-exact-fiber-p solutions)
     (equal
      (amc00p15-transformed-sum solutions)
      (amc00p15-complex-of-rational -1/9)))))

(defun minif2f-amc12-2000-p15-statement ()
  (implies
   (amc00p15-real-closed-field-p)
   (amc00p15-result-p)))

        (value-triple :itpeval-statement-checked)
        :q
