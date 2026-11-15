;; Statement-only formalization of miniF2F artifact amc12b_2021_p18:
        ;; the source complex norm-square equation implies z+6/z=-2 over the full complexification of a real-closed field.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amcb21p18-real-p (value) t)
(defstub amcb21p18-zero () t)
(defstub amcb21p18-one () t)
(defstub amcb21p18-add (left right) t)
(defstub amcb21p18-mul (left right) t)
(defstub amcb21p18-neg (value) t)
(defstub amcb21p18-inv (value) t)
(defstub amcb21p18-lt (left right) t)
(defstub amcb21p18-of-rational (value) t)

(defun amcb21p18-sub (left right)
  (amcb21p18-add left (amcb21p18-neg right)))

(defun amcb21p18-div (left right)
  (amcb21p18-mul left (amcb21p18-inv right)))

(defun amcb21p18-le (left right)
  (or (equal left right) (amcb21p18-lt left right)))

(defun amcb21p18-nonnegative-p (value)
  (and (amcb21p18-real-p value)
       (amcb21p18-le (amcb21p18-zero) value)))

(defun amcb21p18-positive-p (value)
  (and (amcb21p18-real-p value)
       (amcb21p18-lt (amcb21p18-zero) value)))

(defun amcb21p18-abs (value)
  (if (amcb21p18-lt value (amcb21p18-zero))
      (amcb21p18-neg value)
    value))

(defun amcb21p18-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amcb21p18-one)
    (amcb21p18-mul
     value
     (amcb21p18-pow value (1- exponent)))))

(defun-sk amcb21p18-field-laws-p ()
  (forall (x y z)
    (and
     (amcb21p18-real-p (amcb21p18-zero))
     (amcb21p18-real-p (amcb21p18-one))
     (not (equal (amcb21p18-zero) (amcb21p18-one)))
     (implies
      (amcb21p18-real-p x)
      (and
       (amcb21p18-real-p (amcb21p18-neg x))
       (amcb21p18-real-p (amcb21p18-inv x))
       (equal (amcb21p18-add x (amcb21p18-zero)) x)
       (equal (amcb21p18-add x (amcb21p18-neg x))
              (amcb21p18-zero))
       (equal (amcb21p18-mul x (amcb21p18-one)) x)
       (implies
        (not (equal x (amcb21p18-zero)))
        (equal (amcb21p18-mul x (amcb21p18-inv x))
               (amcb21p18-one)))))
     (equal (amcb21p18-inv (amcb21p18-zero))
            (amcb21p18-zero))
     (implies
      (and (amcb21p18-real-p x)
           (amcb21p18-real-p y))
      (and
       (amcb21p18-real-p (amcb21p18-add x y))
       (amcb21p18-real-p (amcb21p18-mul x y))
       (equal (amcb21p18-add x y)
              (amcb21p18-add y x))
       (equal (amcb21p18-mul x y)
              (amcb21p18-mul y x))))
     (implies
      (and (amcb21p18-real-p x)
           (amcb21p18-real-p y)
           (amcb21p18-real-p z))
      (and
       (equal (amcb21p18-add (amcb21p18-add x y) z)
              (amcb21p18-add x (amcb21p18-add y z)))
       (equal (amcb21p18-mul (amcb21p18-mul x y) z)
              (amcb21p18-mul x (amcb21p18-mul y z)))
       (equal (amcb21p18-mul x (amcb21p18-add y z))
              (amcb21p18-add
               (amcb21p18-mul x y)
               (amcb21p18-mul x z))))))))

(defun-sk amcb21p18-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amcb21p18-real-p x)
          (amcb21p18-real-p y)
          (amcb21p18-real-p z))
     (and
      (not (amcb21p18-lt x x))
      (or (equal x y)
          (amcb21p18-lt x y)
          (amcb21p18-lt y x))
      (implies
       (and (amcb21p18-lt x y)
            (amcb21p18-lt y z))
       (amcb21p18-lt x z))
      (implies
       (amcb21p18-lt x y)
       (amcb21p18-lt
        (amcb21p18-add x z)
        (amcb21p18-add y z)))
      (implies
       (and (amcb21p18-lt (amcb21p18-zero) x)
            (amcb21p18-lt (amcb21p18-zero) y))
       (amcb21p18-lt
        (amcb21p18-zero)
        (amcb21p18-mul x y)))))))

(defun-sk amcb21p18-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amcb21p18-real-p (amcb21p18-of-rational a))
      (equal (amcb21p18-of-rational 0) (amcb21p18-zero))
      (equal (amcb21p18-of-rational 1) (amcb21p18-one))
      (equal
       (amcb21p18-of-rational (+ a b))
       (amcb21p18-add
        (amcb21p18-of-rational a)
        (amcb21p18-of-rational b)))
      (equal
       (amcb21p18-of-rational (* a b))
       (amcb21p18-mul
        (amcb21p18-of-rational a)
        (amcb21p18-of-rational b)))
      (equal
       (amcb21p18-of-rational (- a))
       (amcb21p18-neg (amcb21p18-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amcb21p18-of-rational a)
        (amcb21p18-of-rational b)))
      (iff
       (< a b)
       (amcb21p18-lt
        (amcb21p18-of-rational a)
        (amcb21p18-of-rational b)))))))

(defun amcb21p18-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amcb21p18-real-p (car coefficients))
     (amcb21p18-polynomial-p (cdr coefficients)))))

(defun amcb21p18-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amcb21p18-zero)
    (amcb21p18-add
     (car coefficients)
     (amcb21p18-mul
      x
      (amcb21p18-polynomial-value
       (cdr coefficients) x)))))

(defun amcb21p18-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amcb21p18-leading-coefficient (cdr coefficients))))

(defun amcb21p18-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amcb21p18-leading-coefficient coefficients)
     (amcb21p18-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amcb21p18-square-root-exists-p (x)
  (exists (root)
    (and
     (amcb21p18-nonnegative-p root)
     (equal (amcb21p18-mul root root) x))))

(defun-sk amcb21p18-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amcb21p18-nonnegative-p x)
     (amcb21p18-square-root-exists-p x))))

(defun-sk amcb21p18-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amcb21p18-real-p root)
     (equal
      (amcb21p18-polynomial-value coefficients root)
      (amcb21p18-zero)))))

(defun-sk amcb21p18-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amcb21p18-polynomial-p coefficients)
      (amcb21p18-odd-degree-p coefficients))
     (amcb21p18-polynomial-root-exists-p coefficients))))

(defun amcb21p18-real-closed-field-p ()
  (and
   (amcb21p18-field-laws-p)
   (amcb21p18-order-laws-p)
   (amcb21p18-rational-laws-p)
   (amcb21p18-lt (amcb21p18-zero) (amcb21p18-one))
   (amcb21p18-nonnegative-square-roots-p)
   (amcb21p18-odd-polynomial-roots-p)))

(defun amcb21p18-principal-square-root-p (root value)
  (and
   (amcb21p18-nonnegative-p root)
   (equal (amcb21p18-mul root root) value)))

(defchoose amcb21p18-sqrt (root) (value)
  (amcb21p18-principal-square-root-p root value))

(defun amcb21p18-complex-p (value)
  (and (consp value)
       (amcb21p18-real-p (car value))
       (amcb21p18-real-p (cdr value))))

(defun amcb21p18-complex (real imaginary)
  (cons real imaginary))

(defun amcb21p18-complex-zero ()
  (amcb21p18-complex (amcb21p18-zero) (amcb21p18-zero)))

(defun amcb21p18-complex-of-rational (value)
  (amcb21p18-complex
   (amcb21p18-of-rational value)
   (amcb21p18-zero)))

(defun amcb21p18-complex-add (left right)
  (amcb21p18-complex
   (amcb21p18-add (car left) (car right))
   (amcb21p18-add (cdr left) (cdr right))))

(defun amcb21p18-complex-neg (value)
  (amcb21p18-complex
   (amcb21p18-neg (car value))
   (amcb21p18-neg (cdr value))))

(defun amcb21p18-complex-sub (left right)
  (amcb21p18-complex-add left (amcb21p18-complex-neg right)))

(defun amcb21p18-complex-mul (left right)
  (amcb21p18-complex
   (amcb21p18-sub
    (amcb21p18-mul (car left) (car right))
    (amcb21p18-mul (cdr left) (cdr right)))
   (amcb21p18-add
    (amcb21p18-mul (car left) (cdr right))
    (amcb21p18-mul (cdr left) (car right)))))

(defun amcb21p18-complex-norm-square (value)
  (amcb21p18-add
   (amcb21p18-mul (car value) (car value))
   (amcb21p18-mul (cdr value) (cdr value))))

(defun amcb21p18-complex-inv (value)
  (let ((denominator
         (amcb21p18-complex-norm-square value)))
    (amcb21p18-complex
     (amcb21p18-div (car value) denominator)
     (amcb21p18-neg
      (amcb21p18-div (cdr value) denominator)))))

(defun amcb21p18-complex-div (left right)
  (amcb21p18-complex-mul left (amcb21p18-complex-inv right)))

(defun amcb21p18-complex-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amcb21p18-complex-of-rational 1)
    (amcb21p18-complex-mul
     value
     (amcb21p18-complex-pow value (1- exponent)))))

(defun amcb21p18-complex-norm (value)
  (amcb21p18-sqrt (amcb21p18-complex-norm-square value)))

        (defun amc12b-2021-p18-statement (z)
  (let* ((z-plus-two
          (amcb21p18-complex-add
           z
           (amcb21p18-complex-of-rational 2)))
         (z-squared-plus-one
          (amcb21p18-complex-add
           (amcb21p18-complex-pow z 2)
           (amcb21p18-complex-of-rational 1))))
    (implies
     (and
      (amcb21p18-real-closed-field-p)
      (amcb21p18-complex-p z)
      (equal
       (amcb21p18-mul
        (amcb21p18-of-rational 12)
        (amcb21p18-complex-norm-square z))
       (amcb21p18-add
        (amcb21p18-add
         (amcb21p18-mul
          (amcb21p18-of-rational 2)
          (amcb21p18-complex-norm-square z-plus-two))
         (amcb21p18-complex-norm-square
          z-squared-plus-one))
        (amcb21p18-of-rational 31))))
     (equal
      (amcb21p18-complex-add
       z
       (amcb21p18-complex-div
        (amcb21p18-complex-of-rational 6) z))
      (amcb21p18-complex-of-rational -2)))))

        (value-triple :itpeval-statement-checked)
        :q
