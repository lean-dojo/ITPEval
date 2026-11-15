;; Statement-only formalization of miniF2F artifact algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7:
        ;; two linear equations over the full complexification of an arbitrary real-closed field imply f=-10 and z=7.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub lin2c-real-p (value) t)
(defstub lin2c-zero () t)
(defstub lin2c-one () t)
(defstub lin2c-add (left right) t)
(defstub lin2c-mul (left right) t)
(defstub lin2c-neg (value) t)
(defstub lin2c-inv (value) t)
(defstub lin2c-lt (left right) t)
(defstub lin2c-of-rational (value) t)

(defun lin2c-sub (left right)
  (lin2c-add left (lin2c-neg right)))

(defun lin2c-div (left right)
  (lin2c-mul left (lin2c-inv right)))

(defun lin2c-le (left right)
  (or (equal left right) (lin2c-lt left right)))

(defun lin2c-nonnegative-p (value)
  (and (lin2c-real-p value)
       (lin2c-le (lin2c-zero) value)))

(defun lin2c-positive-p (value)
  (and (lin2c-real-p value)
       (lin2c-lt (lin2c-zero) value)))

(defun lin2c-abs (value)
  (if (lin2c-lt value (lin2c-zero))
      (lin2c-neg value)
    value))

(defun lin2c-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (lin2c-one)
    (lin2c-mul
     value
     (lin2c-pow value (1- exponent)))))

(defun-sk lin2c-field-laws-p ()
  (forall (x y z)
    (and
     (lin2c-real-p (lin2c-zero))
     (lin2c-real-p (lin2c-one))
     (not (equal (lin2c-zero) (lin2c-one)))
     (implies
      (lin2c-real-p x)
      (and
       (lin2c-real-p (lin2c-neg x))
       (lin2c-real-p (lin2c-inv x))
       (equal (lin2c-add x (lin2c-zero)) x)
       (equal (lin2c-add x (lin2c-neg x))
              (lin2c-zero))
       (equal (lin2c-mul x (lin2c-one)) x)
       (implies
        (not (equal x (lin2c-zero)))
        (equal (lin2c-mul x (lin2c-inv x))
               (lin2c-one)))))
     (equal (lin2c-inv (lin2c-zero))
            (lin2c-zero))
     (implies
      (and (lin2c-real-p x)
           (lin2c-real-p y))
      (and
       (lin2c-real-p (lin2c-add x y))
       (lin2c-real-p (lin2c-mul x y))
       (equal (lin2c-add x y)
              (lin2c-add y x))
       (equal (lin2c-mul x y)
              (lin2c-mul y x))))
     (implies
      (and (lin2c-real-p x)
           (lin2c-real-p y)
           (lin2c-real-p z))
      (and
       (equal (lin2c-add (lin2c-add x y) z)
              (lin2c-add x (lin2c-add y z)))
       (equal (lin2c-mul (lin2c-mul x y) z)
              (lin2c-mul x (lin2c-mul y z)))
       (equal (lin2c-mul x (lin2c-add y z))
              (lin2c-add
               (lin2c-mul x y)
               (lin2c-mul x z))))))))

(defun-sk lin2c-order-laws-p ()
  (forall (x y z)
    (implies
     (and (lin2c-real-p x)
          (lin2c-real-p y)
          (lin2c-real-p z))
     (and
      (not (lin2c-lt x x))
      (or (equal x y)
          (lin2c-lt x y)
          (lin2c-lt y x))
      (implies
       (and (lin2c-lt x y)
            (lin2c-lt y z))
       (lin2c-lt x z))
      (implies
       (lin2c-lt x y)
       (lin2c-lt
        (lin2c-add x z)
        (lin2c-add y z)))
      (implies
       (and (lin2c-lt (lin2c-zero) x)
            (lin2c-lt (lin2c-zero) y))
       (lin2c-lt
        (lin2c-zero)
        (lin2c-mul x y)))))))

(defun-sk lin2c-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (lin2c-real-p (lin2c-of-rational a))
      (equal (lin2c-of-rational 0) (lin2c-zero))
      (equal (lin2c-of-rational 1) (lin2c-one))
      (equal
       (lin2c-of-rational (+ a b))
       (lin2c-add
        (lin2c-of-rational a)
        (lin2c-of-rational b)))
      (equal
       (lin2c-of-rational (* a b))
       (lin2c-mul
        (lin2c-of-rational a)
        (lin2c-of-rational b)))
      (equal
       (lin2c-of-rational (- a))
       (lin2c-neg (lin2c-of-rational a)))
      (iff
       (equal a b)
       (equal
        (lin2c-of-rational a)
        (lin2c-of-rational b)))
      (iff
       (< a b)
       (lin2c-lt
        (lin2c-of-rational a)
        (lin2c-of-rational b)))))))

(defun lin2c-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (lin2c-real-p (car coefficients))
     (lin2c-polynomial-p (cdr coefficients)))))

(defun lin2c-polynomial-value (coefficients x)
  (if (endp coefficients)
      (lin2c-zero)
    (lin2c-add
     (car coefficients)
     (lin2c-mul
      x
      (lin2c-polynomial-value
       (cdr coefficients) x)))))

(defun lin2c-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (lin2c-leading-coefficient (cdr coefficients))))

(defun lin2c-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (lin2c-leading-coefficient coefficients)
     (lin2c-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk lin2c-square-root-exists-p (x)
  (exists (root)
    (and
     (lin2c-nonnegative-p root)
     (equal (lin2c-mul root root) x))))

(defun-sk lin2c-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (lin2c-nonnegative-p x)
     (lin2c-square-root-exists-p x))))

(defun-sk lin2c-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (lin2c-real-p root)
     (equal
      (lin2c-polynomial-value coefficients root)
      (lin2c-zero)))))

(defun-sk lin2c-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (lin2c-polynomial-p coefficients)
      (lin2c-odd-degree-p coefficients))
     (lin2c-polynomial-root-exists-p coefficients))))

(defun lin2c-real-closed-field-p ()
  (and
   (lin2c-field-laws-p)
   (lin2c-order-laws-p)
   (lin2c-rational-laws-p)
   (lin2c-lt (lin2c-zero) (lin2c-one))
   (lin2c-nonnegative-square-roots-p)
   (lin2c-odd-polynomial-roots-p)))

(defun lin2c-principal-square-root-p (root value)
  (and
   (lin2c-nonnegative-p root)
   (equal (lin2c-mul root root) value)))

(defchoose lin2c-sqrt (root) (value)
  (lin2c-principal-square-root-p root value))

(defun lin2c-complex-p (value)
  (and (consp value)
       (lin2c-real-p (car value))
       (lin2c-real-p (cdr value))))

(defun lin2c-complex (real imaginary)
  (cons real imaginary))

(defun lin2c-complex-zero ()
  (lin2c-complex (lin2c-zero) (lin2c-zero)))

(defun lin2c-complex-of-rational (value)
  (lin2c-complex
   (lin2c-of-rational value)
   (lin2c-zero)))

(defun lin2c-complex-add (left right)
  (lin2c-complex
   (lin2c-add (car left) (car right))
   (lin2c-add (cdr left) (cdr right))))

(defun lin2c-complex-neg (value)
  (lin2c-complex
   (lin2c-neg (car value))
   (lin2c-neg (cdr value))))

(defun lin2c-complex-sub (left right)
  (lin2c-complex-add left (lin2c-complex-neg right)))

(defun lin2c-complex-mul (left right)
  (lin2c-complex
   (lin2c-sub
    (lin2c-mul (car left) (car right))
    (lin2c-mul (cdr left) (cdr right)))
   (lin2c-add
    (lin2c-mul (car left) (cdr right))
    (lin2c-mul (cdr left) (car right)))))

(defun lin2c-complex-norm-square (value)
  (lin2c-add
   (lin2c-mul (car value) (car value))
   (lin2c-mul (cdr value) (cdr value))))

(defun lin2c-complex-inv (value)
  (let ((denominator
         (lin2c-complex-norm-square value)))
    (lin2c-complex
     (lin2c-div (car value) denominator)
     (lin2c-neg
      (lin2c-div (cdr value) denominator)))))

(defun lin2c-complex-div (left right)
  (lin2c-complex-mul left (lin2c-complex-inv right)))

(defun lin2c-complex-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (lin2c-complex-of-rational 1)
    (lin2c-complex-mul
     value
     (lin2c-complex-pow value (1- exponent)))))

(defun lin2c-complex-norm (value)
  (lin2c-sqrt (lin2c-complex-norm-square value)))

        (defun
    algebra-2varlineareq-fp3zeq11-3tfm1m5zeqn68-feqn10-zeq7-statement
    (f z)
  (implies
   (and
    (lin2c-real-closed-field-p)
    (lin2c-complex-p f)
    (lin2c-complex-p z)
    (equal
     (lin2c-complex-add
      f
      (lin2c-complex-mul
       (lin2c-complex-of-rational 3) z))
     (lin2c-complex-of-rational 11))
    (equal
     (lin2c-complex-sub
      (lin2c-complex-mul
       (lin2c-complex-of-rational 3)
       (lin2c-complex-sub
        f
        (lin2c-complex-of-rational 1)))
      (lin2c-complex-mul
       (lin2c-complex-of-rational 5) z))
     (lin2c-complex-of-rational -68)))
   (and
    (equal f (lin2c-complex-of-rational -10))
    (equal z (lin2c-complex-of-rational 7)))))

        (value-triple :itpeval-statement-checked)
        :q
