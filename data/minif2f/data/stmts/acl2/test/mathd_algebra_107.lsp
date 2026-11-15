;; Statement-only formalization of miniF2F artifact mathd_algebra_107:
        ;; the given real quadratic equation is equivalent to the circle (x+4)^2 + (y-3)^2 = 25.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub m107-real-p (value) t)
(defstub m107-zero () t)
(defstub m107-one () t)
(defstub m107-add (left right) t)
(defstub m107-mul (left right) t)
(defstub m107-neg (value) t)
(defstub m107-inv (value) t)
(defstub m107-lt (left right) t)
(defstub m107-of-rational (value) t)

(defun m107-sub (left right)
  (m107-add left (m107-neg right)))

(defun m107-div (left right)
  (m107-mul left (m107-inv right)))

(defun m107-le (left right)
  (or (equal left right) (m107-lt left right)))

(defun m107-nonnegative-p (value)
  (and (m107-real-p value)
       (m107-le (m107-zero) value)))

(defun m107-positive-p (value)
  (and (m107-real-p value)
       (m107-lt (m107-zero) value)))

(defun m107-abs (value)
  (if (m107-lt value (m107-zero))
      (m107-neg value)
    value))

(defun m107-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (m107-one)
    (m107-mul
     value
     (m107-pow value (1- exponent)))))

(defun-sk m107-field-laws-p ()
  (forall (x y z)
    (and
     (m107-real-p (m107-zero))
     (m107-real-p (m107-one))
     (not (equal (m107-zero) (m107-one)))
     (implies
      (m107-real-p x)
      (and
       (m107-real-p (m107-neg x))
       (m107-real-p (m107-inv x))
       (equal (m107-add x (m107-zero)) x)
       (equal (m107-add x (m107-neg x))
              (m107-zero))
       (equal (m107-mul x (m107-one)) x)
       (implies
        (not (equal x (m107-zero)))
        (equal (m107-mul x (m107-inv x))
               (m107-one)))))
     (equal (m107-inv (m107-zero))
            (m107-zero))
     (implies
      (and (m107-real-p x)
           (m107-real-p y))
      (and
       (m107-real-p (m107-add x y))
       (m107-real-p (m107-mul x y))
       (equal (m107-add x y)
              (m107-add y x))
       (equal (m107-mul x y)
              (m107-mul y x))))
     (implies
      (and (m107-real-p x)
           (m107-real-p y)
           (m107-real-p z))
      (and
       (equal (m107-add (m107-add x y) z)
              (m107-add x (m107-add y z)))
       (equal (m107-mul (m107-mul x y) z)
              (m107-mul x (m107-mul y z)))
       (equal (m107-mul x (m107-add y z))
              (m107-add
               (m107-mul x y)
               (m107-mul x z))))))))

(defun-sk m107-order-laws-p ()
  (forall (x y z)
    (implies
     (and (m107-real-p x)
          (m107-real-p y)
          (m107-real-p z))
     (and
      (not (m107-lt x x))
      (or (equal x y)
          (m107-lt x y)
          (m107-lt y x))
      (implies
       (and (m107-lt x y)
            (m107-lt y z))
       (m107-lt x z))
      (implies
       (m107-lt x y)
       (m107-lt
        (m107-add x z)
        (m107-add y z)))
      (implies
       (and (m107-lt (m107-zero) x)
            (m107-lt (m107-zero) y))
       (m107-lt
        (m107-zero)
        (m107-mul x y)))))))

(defun-sk m107-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (m107-real-p (m107-of-rational a))
      (equal (m107-of-rational 0) (m107-zero))
      (equal (m107-of-rational 1) (m107-one))
      (equal
       (m107-of-rational (+ a b))
       (m107-add
        (m107-of-rational a)
        (m107-of-rational b)))
      (equal
       (m107-of-rational (* a b))
       (m107-mul
        (m107-of-rational a)
        (m107-of-rational b)))
      (equal
       (m107-of-rational (- a))
       (m107-neg (m107-of-rational a)))
      (iff
       (equal a b)
       (equal
        (m107-of-rational a)
        (m107-of-rational b)))
      (iff
       (< a b)
       (m107-lt
        (m107-of-rational a)
        (m107-of-rational b)))))))

(defun m107-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (m107-real-p (car coefficients))
     (m107-polynomial-p (cdr coefficients)))))

(defun m107-polynomial-value (coefficients x)
  (if (endp coefficients)
      (m107-zero)
    (m107-add
     (car coefficients)
     (m107-mul
      x
      (m107-polynomial-value
       (cdr coefficients) x)))))

(defun m107-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (m107-leading-coefficient (cdr coefficients))))

(defun m107-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (m107-leading-coefficient coefficients)
     (m107-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk m107-square-root-exists-p (x)
  (exists (root)
    (and
     (m107-nonnegative-p root)
     (equal (m107-mul root root) x))))

(defun-sk m107-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (m107-nonnegative-p x)
     (m107-square-root-exists-p x))))

(defun-sk m107-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (m107-real-p root)
     (equal
      (m107-polynomial-value coefficients root)
      (m107-zero)))))

(defun-sk m107-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (m107-polynomial-p coefficients)
      (m107-odd-degree-p coefficients))
     (m107-polynomial-root-exists-p coefficients))))

(defun m107-real-closed-field-p ()
  (and
   (m107-field-laws-p)
   (m107-order-laws-p)
   (m107-rational-laws-p)
   (m107-lt (m107-zero) (m107-one))
   (m107-nonnegative-square-roots-p)
   (m107-odd-polynomial-roots-p)))

(defun m107-principal-square-root-p (root value)
  (and
   (m107-nonnegative-p root)
   (equal (m107-mul root root) value)))

(defchoose m107-sqrt (root) (value)
  (m107-principal-square-root-p root value))

        (defun mathd-algebra-107-statement (x y)
  (implies
   (and
    (m107-real-closed-field-p)
    (m107-real-p x)
    (m107-real-p y)
    (equal
     (m107-sub
      (m107-add
       (m107-add
        (m107-pow x 2)
        (m107-mul (m107-of-rational 8) x))
       (m107-pow y 2))
      (m107-mul (m107-of-rational 6) y))
     (m107-zero)))
   (equal
    (m107-add
     (m107-pow (m107-add x (m107-of-rational 4)) 2)
     (m107-pow (m107-sub y (m107-of-rational 3)) 2))
    (m107-pow (m107-of-rational 5) 2))))

        (value-triple :itpeval-statement-checked)
        :q
