;; Statement-only formalization of miniF2F artifact mathd_algebra_113:
        ;; the quadratic x^2 - 14x + 3 attains no value below its value at 7.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m113-real-p (value) t)
(defstub m113-zero () t)
(defstub m113-one () t)
(defstub m113-add (left right) t)
(defstub m113-mul (left right) t)
(defstub m113-neg (value) t)
(defstub m113-inv (value) t)
(defstub m113-lt (left right) t)
(defstub m113-of-rational (value) t)

(defun m113-sub (left right)
  (m113-add left (m113-neg right)))

(defun m113-div (left right)
  (m113-mul left (m113-inv right)))

(defun m113-le (left right)
  (or (equal left right) (m113-lt left right)))

(defun m113-nonnegative-p (value)
  (and (m113-real-p value)
       (m113-le (m113-zero) value)))

(defun m113-positive-p (value)
  (and (m113-real-p value)
       (m113-lt (m113-zero) value)))

(defun m113-abs (value)
  (if (m113-lt value (m113-zero))
      (m113-neg value)
    value))

(defun m113-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m113-one)
    (m113-mul
     value
     (m113-pow value (1- exponent)))))

(defun-sk m113-field-laws-p ()
  (forall (x y z)
    (and
     (m113-real-p (m113-zero))
     (m113-real-p (m113-one))
     (not (equal (m113-zero) (m113-one)))
     (implies
      (m113-real-p x)
      (and
       (m113-real-p (m113-neg x))
       (m113-real-p (m113-inv x))
       (equal (m113-add x (m113-zero)) x)
       (equal (m113-add x (m113-neg x))
              (m113-zero))
       (equal (m113-mul x (m113-one)) x)
       (implies
        (not (equal x (m113-zero)))
        (equal (m113-mul x (m113-inv x))
               (m113-one)))))
     (equal (m113-inv (m113-zero))
            (m113-zero))
     (implies
      (and (m113-real-p x)
           (m113-real-p y))
      (and
       (m113-real-p (m113-add x y))
       (m113-real-p (m113-mul x y))
       (equal (m113-add x y)
              (m113-add y x))
       (equal (m113-mul x y)
              (m113-mul y x))))
     (implies
      (and (m113-real-p x)
           (m113-real-p y)
           (m113-real-p z))
      (and
       (equal (m113-add (m113-add x y) z)
              (m113-add x (m113-add y z)))
       (equal (m113-mul (m113-mul x y) z)
              (m113-mul x (m113-mul y z)))
       (equal (m113-mul x (m113-add y z))
              (m113-add
               (m113-mul x y)
               (m113-mul x z))))))))

(defun-sk m113-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m113-real-p x)
          (m113-real-p y)
          (m113-real-p z))
     (and
      (not (m113-lt x x))
      (or (equal x y)
          (m113-lt x y)
          (m113-lt y x))
      (implies
       (and (m113-lt x y)
            (m113-lt y z))
       (m113-lt x z))
      (implies
       (m113-lt x y)
       (m113-lt
        (m113-add x z)
        (m113-add y z)))
      (implies
       (and (m113-lt (m113-zero) x)
            (m113-lt (m113-zero) y))
       (m113-lt
        (m113-zero)
        (m113-mul x y)))))))

(defun-sk m113-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m113-real-p (m113-of-rational a))
      (equal (m113-of-rational 0) (m113-zero))
      (equal (m113-of-rational 1) (m113-one))
      (equal
       (m113-of-rational (+ a b))
       (m113-add
        (m113-of-rational a)
        (m113-of-rational b)))
      (equal
       (m113-of-rational (* a b))
       (m113-mul
        (m113-of-rational a)
        (m113-of-rational b)))
      (equal
       (m113-of-rational (- a))
       (m113-neg (m113-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m113-of-rational a)
        (m113-of-rational b)))
      (iff
       (< a b)
       (m113-lt
        (m113-of-rational a)
        (m113-of-rational b)))))))

(defun m113-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m113-real-p (car coefficients))
     (m113-polynomial-p (cdr coefficients)))))

(defun m113-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m113-zero)
    (m113-add
     (car coefficients)
     (m113-mul
      x
      (m113-polynomial-value
       (cdr coefficients) x)))))

(defun m113-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m113-leading-coefficient (cdr coefficients))))

(defun m113-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m113-leading-coefficient coefficients)
     (m113-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m113-square-root-exists-p (x)
  (exists (root)
    (and
     (m113-nonnegative-p root)
     (equal (m113-mul root root) x))))

(defun-sk m113-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m113-nonnegative-p x)
     (m113-square-root-exists-p x))))

(defun-sk m113-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m113-real-p root)
     (equal
      (m113-polynomial-value coefficients root)
      (m113-zero)))))

(defun-sk m113-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m113-polynomial-p coefficients)
      (m113-odd-degree-p coefficients))
     (m113-polynomial-root-exists-p coefficients))))

(defun m113-real-closed-field-p ()
  (and
   (m113-field-laws-p)
   (m113-order-laws-p)
   (m113-rational-laws-p)
   (m113-lt (m113-zero) (m113-one))
   (m113-nonnegative-square-roots-p)
   (m113-odd-polynomial-roots-p)))

(defun m113-principal-square-root-p (root value)
  (and
   (m113-nonnegative-p root)
   (equal (m113-mul root root) value)))

(defchoose m113-sqrt (root) (value)
  (m113-principal-square-root-p root value))

        (defun m113-quadratic (x)
  (m113-add
   (m113-sub
    (m113-pow x 2)
    (m113-mul (m113-of-rational 14) x))
   (m113-of-rational 3)))

(defun mathd-algebra-113-statement (x)
  (implies
   (and
    (m113-real-closed-field-p)
    (m113-real-p x))
   (m113-le
    (m113-quadratic (m113-of-rational 7))
    (m113-quadratic x))))

        (value-triple :itpeval-statement-checked)
        :q
