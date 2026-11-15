;; Statement-only formalization of miniF2F artifact amc12_2001_p9:
        ;; a real function satisfying f(xy)=f(x)/y for all positive x,y and f(500)=3 must satisfy f(600)=5/2.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amc01p9-real-p (value) t)
(defstub amc01p9-zero () t)
(defstub amc01p9-one () t)
(defstub amc01p9-add (left right) t)
(defstub amc01p9-mul (left right) t)
(defstub amc01p9-neg (value) t)
(defstub amc01p9-inv (value) t)
(defstub amc01p9-lt (left right) t)
(defstub amc01p9-of-rational (value) t)

(defun amc01p9-sub (left right)
  (amc01p9-add left (amc01p9-neg right)))

(defun amc01p9-div (left right)
  (amc01p9-mul left (amc01p9-inv right)))

(defun amc01p9-le (left right)
  (or (equal left right) (amc01p9-lt left right)))

(defun amc01p9-nonnegative-p (value)
  (and (amc01p9-real-p value)
       (amc01p9-le (amc01p9-zero) value)))

(defun amc01p9-positive-p (value)
  (and (amc01p9-real-p value)
       (amc01p9-lt (amc01p9-zero) value)))

(defun amc01p9-abs (value)
  (if (amc01p9-lt value (amc01p9-zero))
      (amc01p9-neg value)
    value))

(defun amc01p9-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amc01p9-one)
    (amc01p9-mul
     value
     (amc01p9-pow value (1- exponent)))))

(defun-sk amc01p9-field-laws-p ()
  (forall (x y z)
    (and
     (amc01p9-real-p (amc01p9-zero))
     (amc01p9-real-p (amc01p9-one))
     (not (equal (amc01p9-zero) (amc01p9-one)))
     (implies
      (amc01p9-real-p x)
      (and
       (amc01p9-real-p (amc01p9-neg x))
       (amc01p9-real-p (amc01p9-inv x))
       (equal (amc01p9-add x (amc01p9-zero)) x)
       (equal (amc01p9-add x (amc01p9-neg x))
              (amc01p9-zero))
       (equal (amc01p9-mul x (amc01p9-one)) x)
       (implies
        (not (equal x (amc01p9-zero)))
        (equal (amc01p9-mul x (amc01p9-inv x))
               (amc01p9-one)))))
     (equal (amc01p9-inv (amc01p9-zero))
            (amc01p9-zero))
     (implies
      (and (amc01p9-real-p x)
           (amc01p9-real-p y))
      (and
       (amc01p9-real-p (amc01p9-add x y))
       (amc01p9-real-p (amc01p9-mul x y))
       (equal (amc01p9-add x y)
              (amc01p9-add y x))
       (equal (amc01p9-mul x y)
              (amc01p9-mul y x))))
     (implies
      (and (amc01p9-real-p x)
           (amc01p9-real-p y)
           (amc01p9-real-p z))
      (and
       (equal (amc01p9-add (amc01p9-add x y) z)
              (amc01p9-add x (amc01p9-add y z)))
       (equal (amc01p9-mul (amc01p9-mul x y) z)
              (amc01p9-mul x (amc01p9-mul y z)))
       (equal (amc01p9-mul x (amc01p9-add y z))
              (amc01p9-add
               (amc01p9-mul x y)
               (amc01p9-mul x z))))))))

(defun-sk amc01p9-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amc01p9-real-p x)
          (amc01p9-real-p y)
          (amc01p9-real-p z))
     (and
      (not (amc01p9-lt x x))
      (or (equal x y)
          (amc01p9-lt x y)
          (amc01p9-lt y x))
      (implies
       (and (amc01p9-lt x y)
            (amc01p9-lt y z))
       (amc01p9-lt x z))
      (implies
       (amc01p9-lt x y)
       (amc01p9-lt
        (amc01p9-add x z)
        (amc01p9-add y z)))
      (implies
       (and (amc01p9-lt (amc01p9-zero) x)
            (amc01p9-lt (amc01p9-zero) y))
       (amc01p9-lt
        (amc01p9-zero)
        (amc01p9-mul x y)))))))

(defun-sk amc01p9-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amc01p9-real-p (amc01p9-of-rational a))
      (equal (amc01p9-of-rational 0) (amc01p9-zero))
      (equal (amc01p9-of-rational 1) (amc01p9-one))
      (equal
       (amc01p9-of-rational (+ a b))
       (amc01p9-add
        (amc01p9-of-rational a)
        (amc01p9-of-rational b)))
      (equal
       (amc01p9-of-rational (* a b))
       (amc01p9-mul
        (amc01p9-of-rational a)
        (amc01p9-of-rational b)))
      (equal
       (amc01p9-of-rational (- a))
       (amc01p9-neg (amc01p9-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amc01p9-of-rational a)
        (amc01p9-of-rational b)))
      (iff
       (< a b)
       (amc01p9-lt
        (amc01p9-of-rational a)
        (amc01p9-of-rational b)))))))

(defun amc01p9-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc01p9-real-p (car coefficients))
     (amc01p9-polynomial-p (cdr coefficients)))))

(defun amc01p9-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amc01p9-zero)
    (amc01p9-add
     (car coefficients)
     (amc01p9-mul
      x
      (amc01p9-polynomial-value
       (cdr coefficients) x)))))

(defun amc01p9-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc01p9-leading-coefficient (cdr coefficients))))

(defun amc01p9-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc01p9-leading-coefficient coefficients)
     (amc01p9-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc01p9-square-root-exists-p (x)
  (exists (root)
    (and
     (amc01p9-nonnegative-p root)
     (equal (amc01p9-mul root root) x))))

(defun-sk amc01p9-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amc01p9-nonnegative-p x)
     (amc01p9-square-root-exists-p x))))

(defun-sk amc01p9-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amc01p9-real-p root)
     (equal
      (amc01p9-polynomial-value coefficients root)
      (amc01p9-zero)))))

(defun-sk amc01p9-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc01p9-polynomial-p coefficients)
      (amc01p9-odd-degree-p coefficients))
     (amc01p9-polynomial-root-exists-p coefficients))))

(defun amc01p9-real-closed-field-p ()
  (and
   (amc01p9-field-laws-p)
   (amc01p9-order-laws-p)
   (amc01p9-rational-laws-p)
   (amc01p9-lt (amc01p9-zero) (amc01p9-one))
   (amc01p9-nonnegative-square-roots-p)
   (amc01p9-odd-polynomial-roots-p)))

(defun amc01p9-principal-square-root-p (root value)
  (and
   (amc01p9-nonnegative-p root)
   (equal (amc01p9-mul root root) value)))

(defchoose amc01p9-sqrt (root) (value)
  (amc01p9-principal-square-root-p root value))

        (defstub amc01p9-f (value) t)

(defun-sk amc01p9-function-closure-p ()
  (forall (x)
    (implies
     (amc01p9-real-p x)
     (amc01p9-real-p (amc01p9-f x)))))

(defun-sk amc01p9-functional-equation-p ()
  (forall (x y)
    (implies
     (and
      (amc01p9-positive-p x)
      (amc01p9-positive-p y))
     (equal
      (amc01p9-f (amc01p9-mul x y))
      (amc01p9-div (amc01p9-f x) y)))))

(defun amc12-2001-p9-statement ()
  (implies
   (and
    (amc01p9-real-closed-field-p)
    (amc01p9-function-closure-p)
    (amc01p9-functional-equation-p)
    (equal
     (amc01p9-f (amc01p9-of-rational 500))
     (amc01p9-of-rational 3)))
   (equal
    (amc01p9-f (amc01p9-of-rational 600))
    (amc01p9-of-rational 5/2))))

        (value-triple :itpeval-statement-checked)
        :q
