;; Statement-only formalization of miniF2F artifact algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2:
        ;; positive reals with 3<=ab+bc+ca satisfy the source cyclic square-root inequality.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub sqrtcyc-real-p (value) t)
(defstub sqrtcyc-zero () t)
(defstub sqrtcyc-one () t)
(defstub sqrtcyc-add (left right) t)
(defstub sqrtcyc-mul (left right) t)
(defstub sqrtcyc-neg (value) t)
(defstub sqrtcyc-inv (value) t)
(defstub sqrtcyc-lt (left right) t)
(defstub sqrtcyc-of-rational (value) t)

(defun sqrtcyc-sub (left right)
  (sqrtcyc-add left (sqrtcyc-neg right)))

(defun sqrtcyc-div (left right)
  (sqrtcyc-mul left (sqrtcyc-inv right)))

(defun sqrtcyc-le (left right)
  (or (equal left right) (sqrtcyc-lt left right)))

(defun sqrtcyc-nonnegative-p (value)
  (and (sqrtcyc-real-p value)
       (sqrtcyc-le (sqrtcyc-zero) value)))

(defun sqrtcyc-positive-p (value)
  (and (sqrtcyc-real-p value)
       (sqrtcyc-lt (sqrtcyc-zero) value)))

(defun sqrtcyc-abs (value)
  (if (sqrtcyc-lt value (sqrtcyc-zero))
      (sqrtcyc-neg value)
    value))

(defun sqrtcyc-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (sqrtcyc-one)
    (sqrtcyc-mul
     value
     (sqrtcyc-pow value (1- exponent)))))

(defun-sk sqrtcyc-field-laws-p ()
  (forall (x y z)
    (and
     (sqrtcyc-real-p (sqrtcyc-zero))
     (sqrtcyc-real-p (sqrtcyc-one))
     (not (equal (sqrtcyc-zero) (sqrtcyc-one)))
     (implies
      (sqrtcyc-real-p x)
      (and
       (sqrtcyc-real-p (sqrtcyc-neg x))
       (sqrtcyc-real-p (sqrtcyc-inv x))
       (equal (sqrtcyc-add x (sqrtcyc-zero)) x)
       (equal (sqrtcyc-add x (sqrtcyc-neg x))
              (sqrtcyc-zero))
       (equal (sqrtcyc-mul x (sqrtcyc-one)) x)
       (implies
        (not (equal x (sqrtcyc-zero)))
        (equal (sqrtcyc-mul x (sqrtcyc-inv x))
               (sqrtcyc-one)))))
     (equal (sqrtcyc-inv (sqrtcyc-zero))
            (sqrtcyc-zero))
     (implies
      (and (sqrtcyc-real-p x)
           (sqrtcyc-real-p y))
      (and
       (sqrtcyc-real-p (sqrtcyc-add x y))
       (sqrtcyc-real-p (sqrtcyc-mul x y))
       (equal (sqrtcyc-add x y)
              (sqrtcyc-add y x))
       (equal (sqrtcyc-mul x y)
              (sqrtcyc-mul y x))))
     (implies
      (and (sqrtcyc-real-p x)
           (sqrtcyc-real-p y)
           (sqrtcyc-real-p z))
      (and
       (equal (sqrtcyc-add (sqrtcyc-add x y) z)
              (sqrtcyc-add x (sqrtcyc-add y z)))
       (equal (sqrtcyc-mul (sqrtcyc-mul x y) z)
              (sqrtcyc-mul x (sqrtcyc-mul y z)))
       (equal (sqrtcyc-mul x (sqrtcyc-add y z))
              (sqrtcyc-add
               (sqrtcyc-mul x y)
               (sqrtcyc-mul x z))))))))

(defun-sk sqrtcyc-order-laws-p ()
  (forall (x y z)
    (implies
     (and (sqrtcyc-real-p x)
          (sqrtcyc-real-p y)
          (sqrtcyc-real-p z))
     (and
      (not (sqrtcyc-lt x x))
      (or (equal x y)
          (sqrtcyc-lt x y)
          (sqrtcyc-lt y x))
      (implies
       (and (sqrtcyc-lt x y)
            (sqrtcyc-lt y z))
       (sqrtcyc-lt x z))
      (implies
       (sqrtcyc-lt x y)
       (sqrtcyc-lt
        (sqrtcyc-add x z)
        (sqrtcyc-add y z)))
      (implies
       (and (sqrtcyc-lt (sqrtcyc-zero) x)
            (sqrtcyc-lt (sqrtcyc-zero) y))
       (sqrtcyc-lt
        (sqrtcyc-zero)
        (sqrtcyc-mul x y)))))))

(defun-sk sqrtcyc-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (sqrtcyc-real-p (sqrtcyc-of-rational a))
      (equal (sqrtcyc-of-rational 0) (sqrtcyc-zero))
      (equal (sqrtcyc-of-rational 1) (sqrtcyc-one))
      (equal
       (sqrtcyc-of-rational (+ a b))
       (sqrtcyc-add
        (sqrtcyc-of-rational a)
        (sqrtcyc-of-rational b)))
      (equal
       (sqrtcyc-of-rational (* a b))
       (sqrtcyc-mul
        (sqrtcyc-of-rational a)
        (sqrtcyc-of-rational b)))
      (equal
       (sqrtcyc-of-rational (- a))
       (sqrtcyc-neg (sqrtcyc-of-rational a)))
      (iff
       (equal a b)
       (equal
        (sqrtcyc-of-rational a)
        (sqrtcyc-of-rational b)))
      (iff
       (< a b)
       (sqrtcyc-lt
        (sqrtcyc-of-rational a)
        (sqrtcyc-of-rational b)))))))

(defun sqrtcyc-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (sqrtcyc-real-p (car coefficients))
     (sqrtcyc-polynomial-p (cdr coefficients)))))

(defun sqrtcyc-polynomial-value (coefficients x)
  (if (endp coefficients)
      (sqrtcyc-zero)
    (sqrtcyc-add
     (car coefficients)
     (sqrtcyc-mul
      x
      (sqrtcyc-polynomial-value
       (cdr coefficients) x)))))

(defun sqrtcyc-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (sqrtcyc-leading-coefficient (cdr coefficients))))

(defun sqrtcyc-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (sqrtcyc-leading-coefficient coefficients)
     (sqrtcyc-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk sqrtcyc-square-root-exists-p (x)
  (exists (root)
    (and
     (sqrtcyc-nonnegative-p root)
     (equal (sqrtcyc-mul root root) x))))

(defun-sk sqrtcyc-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (sqrtcyc-nonnegative-p x)
     (sqrtcyc-square-root-exists-p x))))

(defun-sk sqrtcyc-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (sqrtcyc-real-p root)
     (equal
      (sqrtcyc-polynomial-value coefficients root)
      (sqrtcyc-zero)))))

(defun-sk sqrtcyc-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (sqrtcyc-polynomial-p coefficients)
      (sqrtcyc-odd-degree-p coefficients))
     (sqrtcyc-polynomial-root-exists-p coefficients))))

(defun sqrtcyc-real-closed-field-p ()
  (and
   (sqrtcyc-field-laws-p)
   (sqrtcyc-order-laws-p)
   (sqrtcyc-rational-laws-p)
   (sqrtcyc-lt (sqrtcyc-zero) (sqrtcyc-one))
   (sqrtcyc-nonnegative-square-roots-p)
   (sqrtcyc-odd-polynomial-roots-p)))

(defun sqrtcyc-principal-square-root-p (root value)
  (and
   (sqrtcyc-nonnegative-p root)
   (equal (sqrtcyc-mul root root) value)))

(defchoose sqrtcyc-sqrt (root) (value)
  (sqrtcyc-principal-square-root-p root value))

        (defun algebra-abpbcpcageq3-sumaonsqrtapbgeq3onsqrt2-statement
    (a b c)
  (implies
   (and
    (sqrtcyc-real-closed-field-p)
    (sqrtcyc-positive-p a)
    (sqrtcyc-positive-p b)
    (sqrtcyc-positive-p c)
    (sqrtcyc-le
     (sqrtcyc-of-rational 3)
     (sqrtcyc-add
      (sqrtcyc-add
       (sqrtcyc-mul a b)
       (sqrtcyc-mul b c))
      (sqrtcyc-mul c a))))
   (sqrtcyc-le
    (sqrtcyc-div
     (sqrtcyc-of-rational 3)
     (sqrtcyc-sqrt (sqrtcyc-of-rational 2)))
    (sqrtcyc-add
     (sqrtcyc-add
      (sqrtcyc-div
       a
       (sqrtcyc-sqrt (sqrtcyc-add a b)))
      (sqrtcyc-div
       b
       (sqrtcyc-sqrt (sqrtcyc-add b c))))
     (sqrtcyc-div
      c
      (sqrtcyc-sqrt (sqrtcyc-add c a)))))))

        (value-triple :itpeval-statement-checked)
        :q
