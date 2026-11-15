;; Statement-only formalization of miniF2F artifact aime_1991_p9:
        ;; a unit-circle pair representing sin(x), cos(x), together with the two source trigonometric equations, gives a reduced rational whose numerator and denominator sum to 44.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime91p9-real-p (value) t)
(defstub aime91p9-zero () t)
(defstub aime91p9-one () t)
(defstub aime91p9-add (left right) t)
(defstub aime91p9-mul (left right) t)
(defstub aime91p9-neg (value) t)
(defstub aime91p9-inv (value) t)
(defstub aime91p9-lt (left right) t)
(defstub aime91p9-of-rational (value) t)

(defun aime91p9-sub (left right)
  (aime91p9-add left (aime91p9-neg right)))

(defun aime91p9-div (left right)
  (aime91p9-mul left (aime91p9-inv right)))

(defun aime91p9-le (left right)
  (or (equal left right) (aime91p9-lt left right)))

(defun aime91p9-nonnegative-p (value)
  (and (aime91p9-real-p value)
       (aime91p9-le (aime91p9-zero) value)))

(defun aime91p9-positive-p (value)
  (and (aime91p9-real-p value)
       (aime91p9-lt (aime91p9-zero) value)))

(defun aime91p9-abs (value)
  (if (aime91p9-lt value (aime91p9-zero))
      (aime91p9-neg value)
    value))

(defun aime91p9-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime91p9-one)
    (aime91p9-mul
     value
     (aime91p9-pow value (1- exponent)))))

(defun-sk aime91p9-field-laws-p ()
  (forall (x y z)
    (and
     (aime91p9-real-p (aime91p9-zero))
     (aime91p9-real-p (aime91p9-one))
     (not (equal (aime91p9-zero) (aime91p9-one)))
     (implies
      (aime91p9-real-p x)
      (and
       (aime91p9-real-p (aime91p9-neg x))
       (aime91p9-real-p (aime91p9-inv x))
       (equal (aime91p9-add x (aime91p9-zero)) x)
       (equal (aime91p9-add x (aime91p9-neg x))
              (aime91p9-zero))
       (equal (aime91p9-mul x (aime91p9-one)) x)
       (implies
        (not (equal x (aime91p9-zero)))
        (equal (aime91p9-mul x (aime91p9-inv x))
               (aime91p9-one)))))
     (equal (aime91p9-inv (aime91p9-zero))
            (aime91p9-zero))
     (implies
      (and (aime91p9-real-p x)
           (aime91p9-real-p y))
      (and
       (aime91p9-real-p (aime91p9-add x y))
       (aime91p9-real-p (aime91p9-mul x y))
       (equal (aime91p9-add x y)
              (aime91p9-add y x))
       (equal (aime91p9-mul x y)
              (aime91p9-mul y x))))
     (implies
      (and (aime91p9-real-p x)
           (aime91p9-real-p y)
           (aime91p9-real-p z))
      (and
       (equal (aime91p9-add (aime91p9-add x y) z)
              (aime91p9-add x (aime91p9-add y z)))
       (equal (aime91p9-mul (aime91p9-mul x y) z)
              (aime91p9-mul x (aime91p9-mul y z)))
       (equal (aime91p9-mul x (aime91p9-add y z))
              (aime91p9-add
               (aime91p9-mul x y)
               (aime91p9-mul x z))))))))

(defun-sk aime91p9-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime91p9-real-p x)
          (aime91p9-real-p y)
          (aime91p9-real-p z))
     (and
      (not (aime91p9-lt x x))
      (or (equal x y)
          (aime91p9-lt x y)
          (aime91p9-lt y x))
      (implies
       (and (aime91p9-lt x y)
            (aime91p9-lt y z))
       (aime91p9-lt x z))
      (implies
       (aime91p9-lt x y)
       (aime91p9-lt
        (aime91p9-add x z)
        (aime91p9-add y z)))
      (implies
       (and (aime91p9-lt (aime91p9-zero) x)
            (aime91p9-lt (aime91p9-zero) y))
       (aime91p9-lt
        (aime91p9-zero)
        (aime91p9-mul x y)))))))

(defun-sk aime91p9-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime91p9-real-p (aime91p9-of-rational a))
      (equal (aime91p9-of-rational 0) (aime91p9-zero))
      (equal (aime91p9-of-rational 1) (aime91p9-one))
      (equal
       (aime91p9-of-rational (+ a b))
       (aime91p9-add
        (aime91p9-of-rational a)
        (aime91p9-of-rational b)))
      (equal
       (aime91p9-of-rational (* a b))
       (aime91p9-mul
        (aime91p9-of-rational a)
        (aime91p9-of-rational b)))
      (equal
       (aime91p9-of-rational (- a))
       (aime91p9-neg (aime91p9-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime91p9-of-rational a)
        (aime91p9-of-rational b)))
      (iff
       (< a b)
       (aime91p9-lt
        (aime91p9-of-rational a)
        (aime91p9-of-rational b)))))))

(defun aime91p9-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime91p9-real-p (car coefficients))
     (aime91p9-polynomial-p (cdr coefficients)))))

(defun aime91p9-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime91p9-zero)
    (aime91p9-add
     (car coefficients)
     (aime91p9-mul
      x
      (aime91p9-polynomial-value
       (cdr coefficients) x)))))

(defun aime91p9-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime91p9-leading-coefficient (cdr coefficients))))

(defun aime91p9-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime91p9-leading-coefficient coefficients)
     (aime91p9-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime91p9-square-root-exists-p (x)
  (exists (root)
    (and
     (aime91p9-nonnegative-p root)
     (equal (aime91p9-mul root root) x))))

(defun-sk aime91p9-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime91p9-nonnegative-p x)
     (aime91p9-square-root-exists-p x))))

(defun-sk aime91p9-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime91p9-real-p root)
     (equal
      (aime91p9-polynomial-value coefficients root)
      (aime91p9-zero)))))

(defun-sk aime91p9-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime91p9-polynomial-p coefficients)
      (aime91p9-odd-degree-p coefficients))
     (aime91p9-polynomial-root-exists-p coefficients))))

(defun aime91p9-real-closed-field-p ()
  (and
   (aime91p9-field-laws-p)
   (aime91p9-order-laws-p)
   (aime91p9-rational-laws-p)
   (aime91p9-lt (aime91p9-zero) (aime91p9-one))
   (aime91p9-nonnegative-square-roots-p)
   (aime91p9-odd-polynomial-roots-p)))

(defun aime91p9-principal-square-root-p (root value)
  (and
   (aime91p9-nonnegative-p root)
   (equal (aime91p9-mul root root) value)))

(defchoose aime91p9-sqrt (root) (value)
  (aime91p9-principal-square-root-p root value))

        (defun aime91p9-unit-circle-p (sine-x cosine-x)
  (and
   (aime91p9-real-p sine-x)
   (aime91p9-real-p cosine-x)
   (equal
    (aime91p9-add
     (aime91p9-pow sine-x 2)
     (aime91p9-pow cosine-x 2))
    (aime91p9-one))))

(defun aime-1991-p9-statement (sine-x cosine-x m)
  (let ((tangent-x (aime91p9-div sine-x cosine-x)))
    (implies
     (and
      (aime91p9-real-closed-field-p)
      (aime91p9-unit-circle-p sine-x cosine-x)
      (rationalp m)
      (equal
       (aime91p9-add
        (aime91p9-div (aime91p9-one) cosine-x)
        tangent-x)
       (aime91p9-of-rational 22/7))
      (equal
       (aime91p9-add
        (aime91p9-div (aime91p9-one) sine-x)
        (aime91p9-div (aime91p9-one) tangent-x))
       (aime91p9-of-rational m)))
     (equal
      (+ (denominator m) (numerator m))
      44))))

        (value-triple :itpeval-statement-checked)
        :q
