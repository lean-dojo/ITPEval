;; Statement-only formalization of miniF2F artifact amc12a_2020_p15:
        ;; complex roots of the two source cubics satisfy the stated norm bound over the full complexification of a real-closed field.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca20p15-real-p (value) t)
(defstub amca20p15-zero () t)
(defstub amca20p15-one () t)
(defstub amca20p15-add (left right) t)
(defstub amca20p15-mul (left right) t)
(defstub amca20p15-neg (value) t)
(defstub amca20p15-inv (value) t)
(defstub amca20p15-lt (left right) t)
(defstub amca20p15-of-rational (value) t)

(defun amca20p15-sub (left right)
  (amca20p15-add left (amca20p15-neg right)))

(defun amca20p15-div (left right)
  (amca20p15-mul left (amca20p15-inv right)))

(defun amca20p15-le (left right)
  (or (equal left right) (amca20p15-lt left right)))

(defun amca20p15-nonnegative-p (value)
  (and (amca20p15-real-p value)
       (amca20p15-le (amca20p15-zero) value)))

(defun amca20p15-positive-p (value)
  (and (amca20p15-real-p value)
       (amca20p15-lt (amca20p15-zero) value)))

(defun amca20p15-abs (value)
  (if (amca20p15-lt value (amca20p15-zero))
      (amca20p15-neg value)
    value))

(defun amca20p15-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca20p15-one)
    (amca20p15-mul
     value
     (amca20p15-pow value (1- exponent)))))

(defun-sk amca20p15-field-laws-p ()
  (forall (x y z)
    (and
     (amca20p15-real-p (amca20p15-zero))
     (amca20p15-real-p (amca20p15-one))
     (not (equal (amca20p15-zero) (amca20p15-one)))
     (implies
      (amca20p15-real-p x)
      (and
       (amca20p15-real-p (amca20p15-neg x))
       (amca20p15-real-p (amca20p15-inv x))
       (equal (amca20p15-add x (amca20p15-zero)) x)
       (equal (amca20p15-add x (amca20p15-neg x))
              (amca20p15-zero))
       (equal (amca20p15-mul x (amca20p15-one)) x)
       (implies
        (not (equal x (amca20p15-zero)))
        (equal (amca20p15-mul x (amca20p15-inv x))
               (amca20p15-one)))))
     (equal (amca20p15-inv (amca20p15-zero))
            (amca20p15-zero))
     (implies
      (and (amca20p15-real-p x)
           (amca20p15-real-p y))
      (and
       (amca20p15-real-p (amca20p15-add x y))
       (amca20p15-real-p (amca20p15-mul x y))
       (equal (amca20p15-add x y)
              (amca20p15-add y x))
       (equal (amca20p15-mul x y)
              (amca20p15-mul y x))))
     (implies
      (and (amca20p15-real-p x)
           (amca20p15-real-p y)
           (amca20p15-real-p z))
      (and
       (equal (amca20p15-add (amca20p15-add x y) z)
              (amca20p15-add x (amca20p15-add y z)))
       (equal (amca20p15-mul (amca20p15-mul x y) z)
              (amca20p15-mul x (amca20p15-mul y z)))
       (equal (amca20p15-mul x (amca20p15-add y z))
              (amca20p15-add
               (amca20p15-mul x y)
               (amca20p15-mul x z))))))))

(defun-sk amca20p15-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca20p15-real-p x)
          (amca20p15-real-p y)
          (amca20p15-real-p z))
     (and
      (not (amca20p15-lt x x))
      (or (equal x y)
          (amca20p15-lt x y)
          (amca20p15-lt y x))
      (implies
       (and (amca20p15-lt x y)
            (amca20p15-lt y z))
       (amca20p15-lt x z))
      (implies
       (amca20p15-lt x y)
       (amca20p15-lt
        (amca20p15-add x z)
        (amca20p15-add y z)))
      (implies
       (and (amca20p15-lt (amca20p15-zero) x)
            (amca20p15-lt (amca20p15-zero) y))
       (amca20p15-lt
        (amca20p15-zero)
        (amca20p15-mul x y)))))))

(defun-sk amca20p15-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca20p15-real-p (amca20p15-of-rational a))
      (equal (amca20p15-of-rational 0) (amca20p15-zero))
      (equal (amca20p15-of-rational 1) (amca20p15-one))
      (equal
       (amca20p15-of-rational (+ a b))
       (amca20p15-add
        (amca20p15-of-rational a)
        (amca20p15-of-rational b)))
      (equal
       (amca20p15-of-rational (* a b))
       (amca20p15-mul
        (amca20p15-of-rational a)
        (amca20p15-of-rational b)))
      (equal
       (amca20p15-of-rational (- a))
       (amca20p15-neg (amca20p15-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca20p15-of-rational a)
        (amca20p15-of-rational b)))
      (iff
       (< a b)
       (amca20p15-lt
        (amca20p15-of-rational a)
        (amca20p15-of-rational b)))))))

(defun amca20p15-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca20p15-real-p (car coefficients))
     (amca20p15-polynomial-p (cdr coefficients)))))

(defun amca20p15-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca20p15-zero)
    (amca20p15-add
     (car coefficients)
     (amca20p15-mul
      x
      (amca20p15-polynomial-value
       (cdr coefficients) x)))))

(defun amca20p15-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca20p15-leading-coefficient (cdr coefficients))))

(defun amca20p15-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca20p15-leading-coefficient coefficients)
     (amca20p15-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca20p15-square-root-exists-p (x)
  (exists (root)
    (and
     (amca20p15-nonnegative-p root)
     (equal (amca20p15-mul root root) x))))

(defun-sk amca20p15-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca20p15-nonnegative-p x)
     (amca20p15-square-root-exists-p x))))

(defun-sk amca20p15-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca20p15-real-p root)
     (equal
      (amca20p15-polynomial-value coefficients root)
      (amca20p15-zero)))))

(defun-sk amca20p15-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca20p15-polynomial-p coefficients)
      (amca20p15-odd-degree-p coefficients))
     (amca20p15-polynomial-root-exists-p coefficients))))

(defun amca20p15-real-closed-field-p ()
  (and
   (amca20p15-field-laws-p)
   (amca20p15-order-laws-p)
   (amca20p15-rational-laws-p)
   (amca20p15-lt (amca20p15-zero) (amca20p15-one))
   (amca20p15-nonnegative-square-roots-p)
   (amca20p15-odd-polynomial-roots-p)))

(defun amca20p15-principal-square-root-p (root value)
  (and
   (amca20p15-nonnegative-p root)
   (equal (amca20p15-mul root root) value)))

(defchoose amca20p15-sqrt (root) (value)
  (amca20p15-principal-square-root-p root value))

(defun amca20p15-complex-p (value)
  (and (consp value)
       (amca20p15-real-p (car value))
       (amca20p15-real-p (cdr value))))

(defun amca20p15-complex (real imaginary)
  (cons real imaginary))

(defun amca20p15-complex-zero ()
  (amca20p15-complex (amca20p15-zero) (amca20p15-zero)))

(defun amca20p15-complex-of-rational (value)
  (amca20p15-complex
   (amca20p15-of-rational value)
   (amca20p15-zero)))

(defun amca20p15-complex-add (left right)
  (amca20p15-complex
   (amca20p15-add (car left) (car right))
   (amca20p15-add (cdr left) (cdr right))))

(defun amca20p15-complex-neg (value)
  (amca20p15-complex
   (amca20p15-neg (car value))
   (amca20p15-neg (cdr value))))

(defun amca20p15-complex-sub (left right)
  (amca20p15-complex-add left (amca20p15-complex-neg right)))

(defun amca20p15-complex-mul (left right)
  (amca20p15-complex
   (amca20p15-sub
    (amca20p15-mul (car left) (car right))
    (amca20p15-mul (cdr left) (cdr right)))
   (amca20p15-add
    (amca20p15-mul (car left) (cdr right))
    (amca20p15-mul (cdr left) (car right)))))

(defun amca20p15-complex-norm-square (value)
  (amca20p15-add
   (amca20p15-mul (car value) (car value))
   (amca20p15-mul (cdr value) (cdr value))))

(defun amca20p15-complex-inv (value)
  (let ((denominator
         (amca20p15-complex-norm-square value)))
    (amca20p15-complex
     (amca20p15-div (car value) denominator)
     (amca20p15-neg
      (amca20p15-div (cdr value) denominator)))))

(defun amca20p15-complex-div (left right)
  (amca20p15-complex-mul left (amca20p15-complex-inv right)))

(defun amca20p15-complex-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca20p15-complex-of-rational 1)
    (amca20p15-complex-mul
     value
     (amca20p15-complex-pow value (1- exponent)))))

(defun amca20p15-complex-norm (value)
  (amca20p15-sqrt (amca20p15-complex-norm-square value)))

        (defun amc12a-2020-p15-second-polynomial (b)
  (amca20p15-complex-add
   (amca20p15-complex-sub
    (amca20p15-complex-sub
     (amca20p15-complex-pow b 3)
     (amca20p15-complex-mul
      (amca20p15-complex-of-rational 8)
      (amca20p15-complex-pow b 2)))
    (amca20p15-complex-mul
     (amca20p15-complex-of-rational 8) b))
   (amca20p15-complex-of-rational 64)))

(defun amc12a-2020-p15-statement (a b)
  (implies
   (and
    (amca20p15-real-closed-field-p)
    (amca20p15-complex-p a)
    (amca20p15-complex-p b)
    (equal
     (amca20p15-complex-sub
      (amca20p15-complex-pow a 3)
      (amca20p15-complex-of-rational 8))
     (amca20p15-complex-zero))
    (equal
     (amc12a-2020-p15-second-polynomial b)
     (amca20p15-complex-zero)))
   (amca20p15-le
    (amca20p15-complex-norm
     (amca20p15-complex-sub a b))
    (amca20p15-mul
     (amca20p15-of-rational 2)
     (amca20p15-sqrt
      (amca20p15-of-rational 21))))))

        (value-triple :itpeval-statement-checked)
        :q
