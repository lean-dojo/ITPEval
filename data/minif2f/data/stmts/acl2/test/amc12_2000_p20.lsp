;; Statement-only formalization of miniF2F artifact amc12_2000_p20:
        ;; positive real x, y, z satisfying the three reciprocal equations have product 1.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amc00p20-real-p (value) t)
(defstub amc00p20-zero () t)
(defstub amc00p20-one () t)
(defstub amc00p20-add (left right) t)
(defstub amc00p20-mul (left right) t)
(defstub amc00p20-neg (value) t)
(defstub amc00p20-inv (value) t)
(defstub amc00p20-lt (left right) t)
(defstub amc00p20-of-rational (value) t)

(defun amc00p20-sub (left right)
  (amc00p20-add left (amc00p20-neg right)))

(defun amc00p20-div (left right)
  (amc00p20-mul left (amc00p20-inv right)))

(defun amc00p20-le (left right)
  (or (equal left right) (amc00p20-lt left right)))

(defun amc00p20-nonnegative-p (value)
  (and (amc00p20-real-p value)
       (amc00p20-le (amc00p20-zero) value)))

(defun amc00p20-positive-p (value)
  (and (amc00p20-real-p value)
       (amc00p20-lt (amc00p20-zero) value)))

(defun amc00p20-abs (value)
  (if (amc00p20-lt value (amc00p20-zero))
      (amc00p20-neg value)
    value))

(defun amc00p20-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amc00p20-one)
    (amc00p20-mul
     value
     (amc00p20-pow value (1- exponent)))))

(defun-sk amc00p20-field-laws-p ()
  (forall (x y z)
    (and
     (amc00p20-real-p (amc00p20-zero))
     (amc00p20-real-p (amc00p20-one))
     (not (equal (amc00p20-zero) (amc00p20-one)))
     (implies
      (amc00p20-real-p x)
      (and
       (amc00p20-real-p (amc00p20-neg x))
       (amc00p20-real-p (amc00p20-inv x))
       (equal (amc00p20-add x (amc00p20-zero)) x)
       (equal (amc00p20-add x (amc00p20-neg x))
              (amc00p20-zero))
       (equal (amc00p20-mul x (amc00p20-one)) x)
       (implies
        (not (equal x (amc00p20-zero)))
        (equal (amc00p20-mul x (amc00p20-inv x))
               (amc00p20-one)))))
     (equal (amc00p20-inv (amc00p20-zero))
            (amc00p20-zero))
     (implies
      (and (amc00p20-real-p x)
           (amc00p20-real-p y))
      (and
       (amc00p20-real-p (amc00p20-add x y))
       (amc00p20-real-p (amc00p20-mul x y))
       (equal (amc00p20-add x y)
              (amc00p20-add y x))
       (equal (amc00p20-mul x y)
              (amc00p20-mul y x))))
     (implies
      (and (amc00p20-real-p x)
           (amc00p20-real-p y)
           (amc00p20-real-p z))
      (and
       (equal (amc00p20-add (amc00p20-add x y) z)
              (amc00p20-add x (amc00p20-add y z)))
       (equal (amc00p20-mul (amc00p20-mul x y) z)
              (amc00p20-mul x (amc00p20-mul y z)))
       (equal (amc00p20-mul x (amc00p20-add y z))
              (amc00p20-add
               (amc00p20-mul x y)
               (amc00p20-mul x z))))))))

(defun-sk amc00p20-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amc00p20-real-p x)
          (amc00p20-real-p y)
          (amc00p20-real-p z))
     (and
      (not (amc00p20-lt x x))
      (or (equal x y)
          (amc00p20-lt x y)
          (amc00p20-lt y x))
      (implies
       (and (amc00p20-lt x y)
            (amc00p20-lt y z))
       (amc00p20-lt x z))
      (implies
       (amc00p20-lt x y)
       (amc00p20-lt
        (amc00p20-add x z)
        (amc00p20-add y z)))
      (implies
       (and (amc00p20-lt (amc00p20-zero) x)
            (amc00p20-lt (amc00p20-zero) y))
       (amc00p20-lt
        (amc00p20-zero)
        (amc00p20-mul x y)))))))

(defun-sk amc00p20-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amc00p20-real-p (amc00p20-of-rational a))
      (equal (amc00p20-of-rational 0) (amc00p20-zero))
      (equal (amc00p20-of-rational 1) (amc00p20-one))
      (equal
       (amc00p20-of-rational (+ a b))
       (amc00p20-add
        (amc00p20-of-rational a)
        (amc00p20-of-rational b)))
      (equal
       (amc00p20-of-rational (* a b))
       (amc00p20-mul
        (amc00p20-of-rational a)
        (amc00p20-of-rational b)))
      (equal
       (amc00p20-of-rational (- a))
       (amc00p20-neg (amc00p20-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amc00p20-of-rational a)
        (amc00p20-of-rational b)))
      (iff
       (< a b)
       (amc00p20-lt
        (amc00p20-of-rational a)
        (amc00p20-of-rational b)))))))

(defun amc00p20-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc00p20-real-p (car coefficients))
     (amc00p20-polynomial-p (cdr coefficients)))))

(defun amc00p20-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amc00p20-zero)
    (amc00p20-add
     (car coefficients)
     (amc00p20-mul
      x
      (amc00p20-polynomial-value
       (cdr coefficients) x)))))

(defun amc00p20-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc00p20-leading-coefficient (cdr coefficients))))

(defun amc00p20-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc00p20-leading-coefficient coefficients)
     (amc00p20-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc00p20-square-root-exists-p (x)
  (exists (root)
    (and
     (amc00p20-nonnegative-p root)
     (equal (amc00p20-mul root root) x))))

(defun-sk amc00p20-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amc00p20-nonnegative-p x)
     (amc00p20-square-root-exists-p x))))

(defun-sk amc00p20-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amc00p20-real-p root)
     (equal
      (amc00p20-polynomial-value coefficients root)
      (amc00p20-zero)))))

(defun-sk amc00p20-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc00p20-polynomial-p coefficients)
      (amc00p20-odd-degree-p coefficients))
     (amc00p20-polynomial-root-exists-p coefficients))))

(defun amc00p20-real-closed-field-p ()
  (and
   (amc00p20-field-laws-p)
   (amc00p20-order-laws-p)
   (amc00p20-rational-laws-p)
   (amc00p20-lt (amc00p20-zero) (amc00p20-one))
   (amc00p20-nonnegative-square-roots-p)
   (amc00p20-odd-polynomial-roots-p)))

(defun amc00p20-principal-square-root-p (root value)
  (and
   (amc00p20-nonnegative-p root)
   (equal (amc00p20-mul root root) value)))

(defchoose amc00p20-sqrt (root) (value)
  (amc00p20-principal-square-root-p root value))

        (defun amc12-2000-p20-statement (x y z)
  (implies
   (and
    (amc00p20-real-closed-field-p)
    (amc00p20-positive-p x)
    (amc00p20-positive-p y)
    (amc00p20-positive-p z)
    (equal
     (amc00p20-add
      x
      (amc00p20-div (amc00p20-one) y))
     (amc00p20-of-rational 4))
    (equal
     (amc00p20-add
      y
      (amc00p20-div (amc00p20-one) z))
     (amc00p20-one))
    (equal
     (amc00p20-add
      z
      (amc00p20-div (amc00p20-one) x))
     (amc00p20-of-rational 7/3)))
   (equal
    (amc00p20-mul (amc00p20-mul x y) z)
    (amc00p20-one))))

        (value-triple :itpeval-statement-checked)
        :q
