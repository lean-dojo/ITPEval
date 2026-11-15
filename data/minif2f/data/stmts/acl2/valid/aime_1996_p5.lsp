;; Statement-only formalization of miniF2F artifact aime_1996_p5:
        ;; three distinct complex roots of the source cubic and their three pairwise sums as roots of a second monic cubic imply t=23.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime96p5-real-p (value) t)
(defstub aime96p5-zero () t)
(defstub aime96p5-one () t)
(defstub aime96p5-add (left right) t)
(defstub aime96p5-mul (left right) t)
(defstub aime96p5-neg (value) t)
(defstub aime96p5-inv (value) t)
(defstub aime96p5-lt (left right) t)
(defstub aime96p5-of-rational (value) t)

(defun aime96p5-sub (left right)
  (aime96p5-add left (aime96p5-neg right)))

(defun aime96p5-div (left right)
  (aime96p5-mul left (aime96p5-inv right)))

(defun aime96p5-le (left right)
  (or (equal left right) (aime96p5-lt left right)))

(defun aime96p5-nonnegative-p (value)
  (and (aime96p5-real-p value)
       (aime96p5-le (aime96p5-zero) value)))

(defun aime96p5-positive-p (value)
  (and (aime96p5-real-p value)
       (aime96p5-lt (aime96p5-zero) value)))

(defun aime96p5-abs (value)
  (if (aime96p5-lt value (aime96p5-zero))
      (aime96p5-neg value)
    value))

(defun aime96p5-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime96p5-one)
    (aime96p5-mul
     value
     (aime96p5-pow value (1- exponent)))))

(defun-sk aime96p5-field-laws-p ()
  (forall (x y z)
    (and
     (aime96p5-real-p (aime96p5-zero))
     (aime96p5-real-p (aime96p5-one))
     (not (equal (aime96p5-zero) (aime96p5-one)))
     (implies
      (aime96p5-real-p x)
      (and
       (aime96p5-real-p (aime96p5-neg x))
       (aime96p5-real-p (aime96p5-inv x))
       (equal (aime96p5-add x (aime96p5-zero)) x)
       (equal (aime96p5-add x (aime96p5-neg x))
              (aime96p5-zero))
       (equal (aime96p5-mul x (aime96p5-one)) x)
       (implies
        (not (equal x (aime96p5-zero)))
        (equal (aime96p5-mul x (aime96p5-inv x))
               (aime96p5-one)))))
     (equal (aime96p5-inv (aime96p5-zero))
            (aime96p5-zero))
     (implies
      (and (aime96p5-real-p x)
           (aime96p5-real-p y))
      (and
       (aime96p5-real-p (aime96p5-add x y))
       (aime96p5-real-p (aime96p5-mul x y))
       (equal (aime96p5-add x y)
              (aime96p5-add y x))
       (equal (aime96p5-mul x y)
              (aime96p5-mul y x))))
     (implies
      (and (aime96p5-real-p x)
           (aime96p5-real-p y)
           (aime96p5-real-p z))
      (and
       (equal (aime96p5-add (aime96p5-add x y) z)
              (aime96p5-add x (aime96p5-add y z)))
       (equal (aime96p5-mul (aime96p5-mul x y) z)
              (aime96p5-mul x (aime96p5-mul y z)))
       (equal (aime96p5-mul x (aime96p5-add y z))
              (aime96p5-add
               (aime96p5-mul x y)
               (aime96p5-mul x z))))))))

(defun-sk aime96p5-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime96p5-real-p x)
          (aime96p5-real-p y)
          (aime96p5-real-p z))
     (and
      (not (aime96p5-lt x x))
      (or (equal x y)
          (aime96p5-lt x y)
          (aime96p5-lt y x))
      (implies
       (and (aime96p5-lt x y)
            (aime96p5-lt y z))
       (aime96p5-lt x z))
      (implies
       (aime96p5-lt x y)
       (aime96p5-lt
        (aime96p5-add x z)
        (aime96p5-add y z)))
      (implies
       (and (aime96p5-lt (aime96p5-zero) x)
            (aime96p5-lt (aime96p5-zero) y))
       (aime96p5-lt
        (aime96p5-zero)
        (aime96p5-mul x y)))))))

(defun-sk aime96p5-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime96p5-real-p (aime96p5-of-rational a))
      (equal (aime96p5-of-rational 0) (aime96p5-zero))
      (equal (aime96p5-of-rational 1) (aime96p5-one))
      (equal
       (aime96p5-of-rational (+ a b))
       (aime96p5-add
        (aime96p5-of-rational a)
        (aime96p5-of-rational b)))
      (equal
       (aime96p5-of-rational (* a b))
       (aime96p5-mul
        (aime96p5-of-rational a)
        (aime96p5-of-rational b)))
      (equal
       (aime96p5-of-rational (- a))
       (aime96p5-neg (aime96p5-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime96p5-of-rational a)
        (aime96p5-of-rational b)))
      (iff
       (< a b)
       (aime96p5-lt
        (aime96p5-of-rational a)
        (aime96p5-of-rational b)))))))

(defun aime96p5-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime96p5-real-p (car coefficients))
     (aime96p5-polynomial-p (cdr coefficients)))))

(defun aime96p5-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime96p5-zero)
    (aime96p5-add
     (car coefficients)
     (aime96p5-mul
      x
      (aime96p5-polynomial-value
       (cdr coefficients) x)))))

(defun aime96p5-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime96p5-leading-coefficient (cdr coefficients))))

(defun aime96p5-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime96p5-leading-coefficient coefficients)
     (aime96p5-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime96p5-square-root-exists-p (x)
  (exists (root)
    (and
     (aime96p5-nonnegative-p root)
     (equal (aime96p5-mul root root) x))))

(defun-sk aime96p5-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime96p5-nonnegative-p x)
     (aime96p5-square-root-exists-p x))))

(defun-sk aime96p5-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime96p5-real-p root)
     (equal
      (aime96p5-polynomial-value coefficients root)
      (aime96p5-zero)))))

(defun-sk aime96p5-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime96p5-polynomial-p coefficients)
      (aime96p5-odd-degree-p coefficients))
     (aime96p5-polynomial-root-exists-p coefficients))))

(defun aime96p5-real-closed-field-p ()
  (and
   (aime96p5-field-laws-p)
   (aime96p5-order-laws-p)
   (aime96p5-rational-laws-p)
   (aime96p5-lt (aime96p5-zero) (aime96p5-one))
   (aime96p5-nonnegative-square-roots-p)
   (aime96p5-odd-polynomial-roots-p)))

(defun aime96p5-principal-square-root-p (root value)
  (and
   (aime96p5-nonnegative-p root)
   (equal (aime96p5-mul root root) value)))

(defchoose aime96p5-sqrt (root) (value)
  (aime96p5-principal-square-root-p root value))

(defun aime96p5-complex-p (value)
  (and (consp value)
       (aime96p5-real-p (car value))
       (aime96p5-real-p (cdr value))))

(defun aime96p5-complex (real imaginary)
  (cons real imaginary))

(defun aime96p5-complex-zero ()
  (aime96p5-complex (aime96p5-zero) (aime96p5-zero)))

(defun aime96p5-complex-of-rational (value)
  (aime96p5-complex
   (aime96p5-of-rational value)
   (aime96p5-zero)))

(defun aime96p5-complex-add (left right)
  (aime96p5-complex
   (aime96p5-add (car left) (car right))
   (aime96p5-add (cdr left) (cdr right))))

(defun aime96p5-complex-neg (value)
  (aime96p5-complex
   (aime96p5-neg (car value))
   (aime96p5-neg (cdr value))))

(defun aime96p5-complex-sub (left right)
  (aime96p5-complex-add left (aime96p5-complex-neg right)))

(defun aime96p5-complex-mul (left right)
  (aime96p5-complex
   (aime96p5-sub
    (aime96p5-mul (car left) (car right))
    (aime96p5-mul (cdr left) (cdr right)))
   (aime96p5-add
    (aime96p5-mul (car left) (cdr right))
    (aime96p5-mul (cdr left) (car right)))))

(defun aime96p5-complex-norm-square (value)
  (aime96p5-add
   (aime96p5-mul (car value) (car value))
   (aime96p5-mul (cdr value) (cdr value))))

(defun aime96p5-complex-inv (value)
  (let ((denominator
         (aime96p5-complex-norm-square value)))
    (aime96p5-complex
     (aime96p5-div (car value) denominator)
     (aime96p5-neg
      (aime96p5-div (cdr value) denominator)))))

(defun aime96p5-complex-div (left right)
  (aime96p5-complex-mul left (aime96p5-complex-inv right)))

(defun aime96p5-complex-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime96p5-complex-of-rational 1)
    (aime96p5-complex-mul
     value
     (aime96p5-complex-pow value (1- exponent)))))

(defun aime96p5-complex-norm (value)
  (aime96p5-sqrt (aime96p5-complex-norm-square value)))

        (defun aime96p5-first-polynomial (x)
  (aime96p5-complex-sub
   (aime96p5-complex-add
    (aime96p5-complex-add
     (aime96p5-complex-pow x 3)
     (aime96p5-complex-mul
      (aime96p5-complex-of-rational 3)
      (aime96p5-complex-pow x 2)))
    (aime96p5-complex-mul
     (aime96p5-complex-of-rational 4) x))
   (aime96p5-complex-of-rational 11)))

(defun aime96p5-second-polynomial (r s t-coeff x)
  (aime96p5-complex-add
   (aime96p5-complex-add
    (aime96p5-complex-pow x 3)
    (aime96p5-complex-mul
     r
     (aime96p5-complex-pow x 2)))
   (aime96p5-complex-add
    (aime96p5-complex-mul s x)
    t-coeff)))

(defun aime-1996-p5-statement (a b c r s t-coeff)
  (implies
   (and
    (aime96p5-real-closed-field-p)
    (aime96p5-complex-p a)
    (aime96p5-complex-p b)
    (aime96p5-complex-p c)
    (aime96p5-complex-p r)
    (aime96p5-complex-p s)
    (aime96p5-complex-p t-coeff)
    (equal
     (aime96p5-first-polynomial a)
     (aime96p5-complex-zero))
    (equal
     (aime96p5-first-polynomial b)
     (aime96p5-complex-zero))
    (equal
     (aime96p5-first-polynomial c)
     (aime96p5-complex-zero))
    (equal
     (aime96p5-second-polynomial
      r s t-coeff
      (aime96p5-complex-add a b))
     (aime96p5-complex-zero))
    (equal
     (aime96p5-second-polynomial
      r s t-coeff
      (aime96p5-complex-add b c))
     (aime96p5-complex-zero))
    (equal
     (aime96p5-second-polynomial
      r s t-coeff
      (aime96p5-complex-add c a))
     (aime96p5-complex-zero))
    (not (equal a b))
    (not (equal a c))
    (not (equal b c)))
   (equal
    t-coeff
    (aime96p5-complex-of-rational 23))))

        (value-triple :itpeval-statement-checked)
        :q
