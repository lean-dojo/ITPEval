;; Statement-only formalization of miniF2F artifact aimeI_2000_p7:
        ;; the source positive-real reciprocal system with rational m implies that m's reduced numerator and denominator sum to 5.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aimei00p7-real-p (value) t)
(defstub aimei00p7-zero () t)
(defstub aimei00p7-one () t)
(defstub aimei00p7-add (left right) t)
(defstub aimei00p7-mul (left right) t)
(defstub aimei00p7-neg (value) t)
(defstub aimei00p7-inv (value) t)
(defstub aimei00p7-lt (left right) t)
(defstub aimei00p7-of-rational (value) t)

(defun aimei00p7-sub (left right)
  (aimei00p7-add left (aimei00p7-neg right)))

(defun aimei00p7-div (left right)
  (aimei00p7-mul left (aimei00p7-inv right)))

(defun aimei00p7-le (left right)
  (or (equal left right) (aimei00p7-lt left right)))

(defun aimei00p7-nonnegative-p (value)
  (and (aimei00p7-real-p value)
       (aimei00p7-le (aimei00p7-zero) value)))

(defun aimei00p7-positive-p (value)
  (and (aimei00p7-real-p value)
       (aimei00p7-lt (aimei00p7-zero) value)))

(defun aimei00p7-abs (value)
  (if (aimei00p7-lt value (aimei00p7-zero))
      (aimei00p7-neg value)
    value))

(defun aimei00p7-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aimei00p7-one)
    (aimei00p7-mul
     value
     (aimei00p7-pow value (1- exponent)))))

(defun-sk aimei00p7-field-laws-p ()
  (forall (x y z)
    (and
     (aimei00p7-real-p (aimei00p7-zero))
     (aimei00p7-real-p (aimei00p7-one))
     (not (equal (aimei00p7-zero) (aimei00p7-one)))
     (implies
      (aimei00p7-real-p x)
      (and
       (aimei00p7-real-p (aimei00p7-neg x))
       (aimei00p7-real-p (aimei00p7-inv x))
       (equal (aimei00p7-add x (aimei00p7-zero)) x)
       (equal (aimei00p7-add x (aimei00p7-neg x))
              (aimei00p7-zero))
       (equal (aimei00p7-mul x (aimei00p7-one)) x)
       (implies
        (not (equal x (aimei00p7-zero)))
        (equal (aimei00p7-mul x (aimei00p7-inv x))
               (aimei00p7-one)))))
     (equal (aimei00p7-inv (aimei00p7-zero))
            (aimei00p7-zero))
     (implies
      (and (aimei00p7-real-p x)
           (aimei00p7-real-p y))
      (and
       (aimei00p7-real-p (aimei00p7-add x y))
       (aimei00p7-real-p (aimei00p7-mul x y))
       (equal (aimei00p7-add x y)
              (aimei00p7-add y x))
       (equal (aimei00p7-mul x y)
              (aimei00p7-mul y x))))
     (implies
      (and (aimei00p7-real-p x)
           (aimei00p7-real-p y)
           (aimei00p7-real-p z))
      (and
       (equal (aimei00p7-add (aimei00p7-add x y) z)
              (aimei00p7-add x (aimei00p7-add y z)))
       (equal (aimei00p7-mul (aimei00p7-mul x y) z)
              (aimei00p7-mul x (aimei00p7-mul y z)))
       (equal (aimei00p7-mul x (aimei00p7-add y z))
              (aimei00p7-add
               (aimei00p7-mul x y)
               (aimei00p7-mul x z))))))))

(defun-sk aimei00p7-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aimei00p7-real-p x)
          (aimei00p7-real-p y)
          (aimei00p7-real-p z))
     (and
      (not (aimei00p7-lt x x))
      (or (equal x y)
          (aimei00p7-lt x y)
          (aimei00p7-lt y x))
      (implies
       (and (aimei00p7-lt x y)
            (aimei00p7-lt y z))
       (aimei00p7-lt x z))
      (implies
       (aimei00p7-lt x y)
       (aimei00p7-lt
        (aimei00p7-add x z)
        (aimei00p7-add y z)))
      (implies
       (and (aimei00p7-lt (aimei00p7-zero) x)
            (aimei00p7-lt (aimei00p7-zero) y))
       (aimei00p7-lt
        (aimei00p7-zero)
        (aimei00p7-mul x y)))))))

(defun-sk aimei00p7-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aimei00p7-real-p (aimei00p7-of-rational a))
      (equal (aimei00p7-of-rational 0) (aimei00p7-zero))
      (equal (aimei00p7-of-rational 1) (aimei00p7-one))
      (equal
       (aimei00p7-of-rational (+ a b))
       (aimei00p7-add
        (aimei00p7-of-rational a)
        (aimei00p7-of-rational b)))
      (equal
       (aimei00p7-of-rational (* a b))
       (aimei00p7-mul
        (aimei00p7-of-rational a)
        (aimei00p7-of-rational b)))
      (equal
       (aimei00p7-of-rational (- a))
       (aimei00p7-neg (aimei00p7-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aimei00p7-of-rational a)
        (aimei00p7-of-rational b)))
      (iff
       (< a b)
       (aimei00p7-lt
        (aimei00p7-of-rational a)
        (aimei00p7-of-rational b)))))))

(defun aimei00p7-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aimei00p7-real-p (car coefficients))
     (aimei00p7-polynomial-p (cdr coefficients)))))

(defun aimei00p7-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aimei00p7-zero)
    (aimei00p7-add
     (car coefficients)
     (aimei00p7-mul
      x
      (aimei00p7-polynomial-value
       (cdr coefficients) x)))))

(defun aimei00p7-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aimei00p7-leading-coefficient (cdr coefficients))))

(defun aimei00p7-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aimei00p7-leading-coefficient coefficients)
     (aimei00p7-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aimei00p7-square-root-exists-p (x)
  (exists (root)
    (and
     (aimei00p7-nonnegative-p root)
     (equal (aimei00p7-mul root root) x))))

(defun-sk aimei00p7-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aimei00p7-nonnegative-p x)
     (aimei00p7-square-root-exists-p x))))

(defun-sk aimei00p7-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aimei00p7-real-p root)
     (equal
      (aimei00p7-polynomial-value coefficients root)
      (aimei00p7-zero)))))

(defun-sk aimei00p7-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aimei00p7-polynomial-p coefficients)
      (aimei00p7-odd-degree-p coefficients))
     (aimei00p7-polynomial-root-exists-p coefficients))))

(defun aimei00p7-real-closed-field-p ()
  (and
   (aimei00p7-field-laws-p)
   (aimei00p7-order-laws-p)
   (aimei00p7-rational-laws-p)
   (aimei00p7-lt (aimei00p7-zero) (aimei00p7-one))
   (aimei00p7-nonnegative-square-roots-p)
   (aimei00p7-odd-polynomial-roots-p)))

(defun aimei00p7-principal-square-root-p (root value)
  (and
   (aimei00p7-nonnegative-p root)
   (equal (aimei00p7-mul root root) value)))

(defchoose aimei00p7-sqrt (root) (value)
  (aimei00p7-principal-square-root-p root value))

        (defun aimei-2000-p7-statement (x y z m)
  (implies
   (and
    (aimei00p7-real-closed-field-p)
    (aimei00p7-positive-p x)
    (aimei00p7-positive-p y)
    (aimei00p7-positive-p z)
    (rationalp m)
    (< 0 m)
    (equal
     (aimei00p7-mul (aimei00p7-mul x y) z)
     (aimei00p7-one))
    (equal
     (aimei00p7-add
      x
      (aimei00p7-div (aimei00p7-one) z))
     (aimei00p7-of-rational 5))
    (equal
     (aimei00p7-add
      y
      (aimei00p7-div (aimei00p7-one) x))
     (aimei00p7-of-rational 29))
    (equal
     (aimei00p7-add
      z
      (aimei00p7-div (aimei00p7-one) y))
     (aimei00p7-of-rational m)))
   (equal
    (+ (denominator m) (numerator m))
    5)))

        (value-triple :itpeval-statement-checked)
        :q
